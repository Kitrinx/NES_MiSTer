// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

// altera message_off 10935
// altera message_off 10027

// Generates the current scanline / cycle counters
module ClockGen(
	input  logic       clk,
	input  logic       ce,
	input  logic       ce2,
	input  logic       reset,
	input  logic [1:0] sys_type,
	input  logic       rendering_enabled,
	output logic       held_reset,
	output logic [8:0] scanline,
	output logic [8:0] cycle,
	output logic       end_of_line,
	output logic       at_last_cycle_group,
	output logic       exiting_vblank,
	output logic       entering_vblank,
	output logic       short_frame,
	output logic       clr_vbl_ovf_sp0,
	output logic       is_pre_render,
	output logic       is_visible,
	output logic       is_rendering,
	output logic       pclk0,        // Phase clock 0
	output logic       pclk1,         // Phase clock 1
	output logic       is_vbe_sl
);

// State
logic even_frame_toggle = 0; // 1 indicates even frame.

// Ephmeral state
logic [1:0] clk_delay;

// Nonvolatile State
logic [8:0] vblank_start_sl;
logic [8:0] vblank_end_sl;
logic skip_en;

// Continuous Intermediates
logic skip_dot;

assign pclk0 = ce;
assign pclk1 = ce2;

// The pre render flag is set while we're on scanline -1.
assign is_rendering = rendering_enabled & (is_visible | is_pre_render);
assign at_last_cycle_group = (cycle[8:3] == 42);
assign end_of_line = at_last_cycle_group && (cycle[2:0] == (skip_dot ? 3 : 4));

// For NTSC only, the *last* cycle of odd frames is skipped. This signal is for de-jitter.
assign short_frame = end_of_line & skip_dot;

// All vblank clocked registers should have changed and be readable by cycle 1 of the vblank scanlines
assign entering_vblank = (cycle == 0) && scanline == vblank_start_sl;
assign exiting_vblank = (cycle == 0) && is_pre_render;

assign is_vbe_sl = (scanline == vblank_end_sl);
// This flag clears the sprite zero hit, sprite overflow, held_reset, and is_visible registers
assign clr_vbl_ovf_sp0 = is_vbe_sl && end_of_line;



always @(posedge clk) if (reset) begin
	cycle <= 9'd0;
	scanline <= 9'd0;
	even_frame_toggle <= 1; // Resets to 0.
	held_reset <= 1;
	is_visible <= 0;

	case (sys_type)
		2'b00,2'b11: begin // NTSC/Vs.
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd260;
			skip_en         <= 1'b1;
		end

		2'b01: begin       // PAL
			vblank_start_sl <= 9'd241;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end

		2'b10: begin       // Dendy
			vblank_start_sl <= 9'd291;
			vblank_end_sl   <= 9'd310;
			skip_en         <= 1'b0;
		end
	endcase
end else begin
	if (pclk1) // The determinaton to advance to the next line is made at pclk1
		skip_dot <= is_pre_render && ~even_frame_toggle && is_rendering && skip_en;

	if (pclk0) begin
		cycle <= cycle + 9'd1;
		if (clr_vbl_ovf_sp0) begin
			held_reset <= 0;
			is_visible <= 1;
		end

		if (end_of_line) begin
			cycle <= 9'd0;

			if (scanline == 239)
				is_visible <= 0;
			// Once the scanline counter reaches end of 260, it gets reset to -1.
			if (scanline == vblank_end_sl) begin
				scanline <= 9'd511;
				is_pre_render <= 1;
			end else begin
				scanline <= scanline + 1'd1;
				is_pre_render <= 0;
			end

			if (scanline == 255)
				even_frame_toggle <= ~even_frame_toggle;
		end
	end
end

endmodule // ClockGen

module VramGen (
	input  logic        clk,
	input  logic        reset,
	input  logic        ce,
	input  logic        pclk1,
	input  logic        read_ce,
	input  logic        write_ce,
	input  logic        is_rendering,
	input  logic        rendering_enabled,
	input  logic  [2:0] ain,           // input address from CPU
	input  logic  [7:0] din,           // data input
	input  logic        read,          // read
	input  logic        write,         // write
	input  logic        is_pre_render, // Is this the pre-render scanline
	input  logic  [8:0] cycle,
	input  logic        ppu_incr,
	input  logic        HVTog,
	output logic [14:0] vram_v,
	output logic  [2:0] fine_x_scroll  // Current fine_x_scroll value
);

// Temporary VRAM address register
logic [14:0] vram_t;

// SR To delay 2006 copy to vram_v
logic [3:0] delayed_2006_write;
logic pending_2006_trig;

// Other intermediates
logic [14:0] vram_t_mask;
logic trigger_2007;
logic trigger_2007_cur;
logic trigger_2007_latch;

logic write_2006, write_2006_1, write_2006_2;

// VRAM_v reference:
// [14 13 12] [11 10] [9 8 7 6 5] [4 3 2 1 0]
//  Fine Y     NT Sel  Coarse Y    Coarse X
// Fine X is its own seperate register.

// Performs the glitchy vram_scroll used by Burai Fighter and some others
// FIXME: Assumes 1 pclk0 tick per read/write. Should be delayed to falling edge of phi2?
assign trigger_2007 = (trigger_2007_cur && (read_n || write_n)) | trigger_2007_latch;
// Mask used to simulate glitchy behavior caused by a 2006 delayed write landing on the same cycle
// as natural copy from t->v
assign vram_t_mask = write_2006 ? vram_t : 15'h7FFF;

logic read_n;
logic write_n;
logic old_read;
logic old_write;

assign read_n = ~read & old_read;
assign write_n = ~write & old_write;

always @(posedge clk) if (reset) begin
	vram_t <= 0;
	fine_x_scroll <= 0;
end else begin
	old_read <= read;
	old_write <= write;

	 trigger_2007_cur <= ((read || write) && ain == 7);

	if (read_n || write_n)
		trigger_2007_latch <= trigger_2007_cur;

	// Copies from T to V are delayed by 1 pclk1 and then 2 pclk0 cycles after the second 2006 write
	if (pclk1) begin
		pending_2006_trig <= 0;
		write_2006_1 <= pending_2006_trig;
	end

	if (ce) begin
		trigger_2007_latch <= 0;
		write_2006_2 <= write_2006_1;
		write_2006 <= write_2006_2;

		// Horizontal copy at cycle 257 and rendering OR if delayed 2006 write
		if (is_rendering && cycle == 256 || write_2006)
			{vram_v[10], vram_v[4:0]} <= {vram_t[10], vram_t[4:0]};

		// Vertical copy at Cycles 280 to 305 and rendering OR delayed 2006 write
		if (cycle >= 279 && cycle < 304 && is_pre_render && rendering_enabled || write_2006)
			{vram_v[14:11], vram_v[9:5]} <= {vram_t[14:11], vram_t[9:5]};

		// Increment course X scroll from (cycle 0-255 or 320-335) and cycle[2:0] == 7
		if (is_rendering && ((cycle[2:0] == 7 && (~cycle[8] || (cycle[8] && cycle[6]))) || trigger_2007)) begin
			vram_v[4:0] <= (vram_v[4:0] + 1'd1) & vram_t_mask[4:0];
			vram_v[10] <= (vram_v[10] ^ &vram_v[4:0]) & vram_t_mask[10];
		end

		// Vertical Increment at 256 and rendering
		if (is_rendering && (cycle == 255 || trigger_2007)) begin
			vram_v[14:12] <= (vram_v[14:12] + 1'd1) & vram_t_mask[14:12];
			vram_v[9:5] <= vram_v[9:5] & vram_t_mask[9:5];
			vram_v[11] <= vram_v[11] & vram_t_mask[11];
			if (vram_v[14:12] == 7) begin
				if (vram_v[9:5] == 29) begin
					vram_v[9:5] <= 0;
					vram_v[11] <= ~vram_v[11] & vram_t_mask[11];
				end else begin
					vram_v[9:5] <= (vram_v[9:5] + 1'd1) & vram_t_mask[9:5];
				end
			end
		end
	end

	if (write_ce && ain == 6 && HVTog)
		pending_2006_trig <= 1;

	if (write && ain == 0) begin
		vram_t[10] <= din[0];
		vram_t[11] <= din[1];
	end else if (write && ain == 5) begin
		if (!HVTog) begin
			vram_t[4:0] <= din[7:3];
			fine_x_scroll <= din[2:0];
		end else begin
			vram_t[9:5] <= din[7:3];
			vram_t[14:12] <= din[2:0];
		end
	end else if (write && ain == 6) begin
		if (!HVTog) begin
			vram_t[13:8] <= din[5:0];
			vram_t[14] <= 0;
		end else begin
			vram_t[7:0] <= din;
		end
	end else if (trigger_2007_cur && (read_n || write_n) && ~is_rendering) begin
		// Increment address every time we accessed a reg
		vram_v <= vram_v + (ppu_incr ? 15'd32 : 15'd1);
	end
end

endmodule

// Generates the current scanline / cycle counters
module ClockGenOld(
	input clk,
	input ce,
	input reset,
	input [1:0] sys_type,
	input is_rendering,
	output reg [8:0] scanline,
	output reg [8:0] cycle,
	output reg is_in_vblank,
	output end_of_line,
	output at_last_cycle_group,
	output exiting_vblank,
	output entering_vblank,
	output reg is_pre_render,
	output short_frame,
	output is_vbe_sl
);

reg even_frame_toggle = 0; // 1 indicates even frame.

// Dendy is 291 to 310
wire [8:0] vblank_start_sl;
wire [8:0] vblank_end_sl;
wire [8:0] last_sl;
wire skip_en;
reg [3:0] rendering_sr;

always_comb begin
	case (sys_type)
		2'b00,2'b11: begin // NTSC/Vs.
			vblank_start_sl = 9'd241;
			vblank_end_sl   = 9'd260;
			skip_en         = 1'b1;
		end

		2'b01: begin       // PAL
			vblank_start_sl = 9'd241;
			vblank_end_sl   = 9'd310;
			skip_en         = 1'b0;
		end

		2'b10: begin       // Dendy
			vblank_start_sl = 9'd291;
			vblank_end_sl   = 9'd310;
			skip_en         = 1'b0;
		end
	endcase
end

assign at_last_cycle_group = (cycle[8:3] == 42);

// For NTSC only, the *last* cycle of odd frames is skipped.
// In Visual 2C02, the counter starts at zero and flips at scanline 256.
assign short_frame = end_of_line & skip_pixel;

wire skip_pixel = is_pre_render && ~even_frame_toggle && rendering_sr[3] && skip_en;
assign end_of_line = at_last_cycle_group && (cycle[3:0] == (skip_pixel ? 3 : 4));

// Confimed with Visual 2C02
// All vblank clocked registers should have changed and be readable by cycle 1 of 241/261
assign entering_vblank = (cycle == 0) && scanline == vblank_start_sl;
assign exiting_vblank = (cycle == 0) && is_pre_render;

assign is_vbe_sl = (scanline == vblank_end_sl);

// New value for is_in_vblank flag
wire new_is_in_vblank = entering_vblank ? 1'b1 : exiting_vblank ? 1'b0 : is_in_vblank;

// Set if the current line is line 0..239
always @(posedge clk) if (reset) begin
	cycle <= 338;
	is_in_vblank <= 0;
end else if (ce) begin
	// On a real AV famicom, the NMI even_odd_timing test fails with 09, this SR is to make that happen
	rendering_sr <= {rendering_sr[2:0], is_rendering};
	cycle <= end_of_line ? 9'd0 : cycle + 9'd1;
	is_in_vblank <= new_is_in_vblank;
end

always @(posedge clk) if (reset) begin
	scanline <= 0;
	is_pre_render <= 0;
	even_frame_toggle <= 0; // Resets to 0, the first frame will always end with 341 pixels.
end else if (ce && end_of_line) begin
	// Once the scanline counter reaches end of 260, it gets reset to -1.
	scanline <= (scanline == vblank_end_sl) ? 9'b111111111 : scanline + 1'd1;
	// The pre render flag is set while we're on scanline -1.
	is_pre_render <= (scanline == vblank_end_sl);

	if (scanline == 255)
		even_frame_toggle <= ~even_frame_toggle;
end

endmodule // ClockGen

// 8 of these exist, they are used to output sprites.
module Sprite(
	input clk,
	input ce,
	input enable,
	input [3:0] load,
	input [26:0] load_in,
	output [26:0] load_out,
	output [4:0] bits // Low 4 bits = pixel, high bit = prio
);

reg [1:0] upper_color; // Upper 2 bits of color
reg [7:0] x_coord;     // X coordinate where we want things
reg [7:0] pix1, pix2;  // Shift registers, output when x_coord == 0
reg aprio;             // Current prio
wire active = (x_coord == 0);

always @(posedge clk) if (ce) begin
	if (enable) begin
		if (!active) begin
			// Decrease until x_coord is zero.
			x_coord <= x_coord - 8'h01;
		end else begin
			pix1 <= pix1 >> 1;
			pix2 <= pix2 >> 1;
		end
	end
	if (load[3]) pix1 <= load_in[26:19];
	if (load[2]) pix2 <= load_in[18:11];
	if (load[1]) x_coord <= load_in[10:3];
	if (load[0]) {upper_color, aprio} <= load_in[2:0];
end
assign bits = {aprio, upper_color, active && pix2[0], active && pix1[0]};
assign load_out = {pix1, pix2, x_coord, upper_color, aprio};

endmodule  // SpriteGen

// This contains all sprites. Will return the pixel value of the highest prioritized sprite.
// When load is set, and clocked, load_in is loaded into sprite 15 and all others are shifted down.
// Sprite 0 has highest prio.
module SpriteSet(
	input clk,
	input ce,               // Input clock
	input enable,           // Enable pixel generation
	input [3:0] load,       // Which parts of the state to load/shift.
	input [3:0] load_ex,    // Which parts of the state to load/shift for extra sprites.
	input [26:0] load_in,   // State to load with
	input [26:0] load_in_ex,// Extra spirtes
	output [4:0] bits,      // Output bits
	output is_sprite0,       // Set to true if sprite #0 was output
	input extra_sprites
);

wire [26:0] load_out7, load_out6, load_out5, load_out4, load_out3, load_out2, load_out1, load_out0,
	load_out15, load_out14, load_out13, load_out12, load_out11, load_out10, load_out9, load_out8;
wire [4:0] bits7, bits6, bits5, bits4, bits3, bits2, bits1, bits0,
	bits15, bits14, bits13, bits12, bits11, bits10, bits9, bits8;

// Extra sprites
Sprite sprite15(clk, ce, enable, load_ex, load_in_ex, load_out15, bits15);
Sprite sprite14(clk, ce, enable, load_ex, load_out15, load_out14, bits14);
Sprite sprite13(clk, ce, enable, load_ex, load_out14, load_out13, bits13);
Sprite sprite12(clk, ce, enable, load_ex, load_out13, load_out12, bits12);
Sprite sprite11(clk, ce, enable, load_ex, load_out12, load_out11, bits11);
Sprite sprite10(clk, ce, enable, load_ex, load_out11, load_out10, bits10);
Sprite sprite9( clk, ce, enable, load_ex, load_out10, load_out9,  bits9);
Sprite sprite8( clk, ce, enable, load_ex, load_out9,  load_out8,  bits8);

// Basic Sprites
Sprite sprite7( clk, ce, enable, load, load_in,    load_out7,  bits7);
Sprite sprite6( clk, ce, enable, load, load_out7,  load_out6,  bits6);
Sprite sprite5( clk, ce, enable, load, load_out6,  load_out5,  bits5);
Sprite sprite4( clk, ce, enable, load, load_out5,  load_out4,  bits4);
Sprite sprite3( clk, ce, enable, load, load_out4,  load_out3,  bits3);
Sprite sprite2( clk, ce, enable, load, load_out3,  load_out2,  bits2);
Sprite sprite1( clk, ce, enable, load, load_out2,  load_out1,  bits1);
Sprite sprite0( clk, ce, enable, load, load_out1,  load_out0,  bits0);

// Determine which sprite is visible on this pixel.
assign bits = bits_orig;
wire [4:0] bits_orig =
	bits0[1:0]  != 0 ? bits0 :
	bits1[1:0]  != 0 ? bits1 :
	bits2[1:0]  != 0 ? bits2 :
	bits3[1:0]  != 0 ? bits3 :
	bits4[1:0]  != 0 ? bits4 :
	bits5[1:0]  != 0 ? bits5 :
	bits6[1:0]  != 0 ? bits6 :
	bits7[1:0]  != 0 || ~extra_sprites ? bits7 :
	bits_ex;

wire [4:0] bits_ex =
	bits8[1:0]  != 0 ? bits8 :
	bits9[1:0]  != 0 ? bits9 :
	bits10[1:0] != 0 ? bits10 :
	bits11[1:0] != 0 ? bits11 :
	bits12[1:0] != 0 ? bits12 :
	bits13[1:0] != 0 ? bits13 :
	bits14[1:0] != 0 ? bits14 :
	bits15;

assign is_sprite0 = bits0[1:0] != 0;

endmodule  // SpriteSet

module OAMEval(
	input clk,
	input ce,
	input reset,
	input rendering_enabled,   // Set to 1 if evaluations are enabled
	input obj_size,            // Set to 1 if objects are 16 pixels.
	input [8:0] scanline,      // Current scan line (compared against Y)
	input [8:0] cycle,         // Current cycle.
	output [7:0] oam_bus,      // Current value on the OAM bus, returned to NES through $2004.
	output reg [31:0] oam_bus_ex,
	input oam_addr_write,      // Load oam with specified value, when writing to NES $2003.
	input oam_data_write,      // Load oam_ptr with specified value, when writing to NES $2004.
	input [7:0] oam_din,       // New value for oam or oam_ptr
	output reg spr_overflow,   // Set to true if we had more than 8 objects on a scan line. Reset when exiting vblank.
	output reg sprite0,        // True if sprite#0 is included on the scan line currently being painted.
	input is_vbe,              // Last line before pre-render
	input PAL,
	output masked_sprites      // If the game is trying to mask extra sprites
);

// https://wiki.nesdev.com/w/index.php/PPU_sprite_evaluation
// NOTE: At the time of this writing, much information on the wiki is off by one, as mentioned here:
// https://forums.nesdev.com/viewtopic.php?f=3&t=19005

assign oam_bus = oam_data;

enum {
	STATE_IDLE,
	STATE_CLEAR,
	STATE_EVAL,
	STATE_FETCH,
	STATE_REFRESH
} oam_state = STATE_IDLE;

reg [7:0] oam_temp[64];    // OAM Temporary buffer, normally 32 bytes, 64 for extra sprites
reg [7:0] oam[256];        // OAM RAM, 256 bytes
reg [7:0] oam_addr;        // OAM Address Register 2003
reg [2:0] oam_temp_slot;   // Pointer to oam_temp;
reg [7:0] oam_data;        // OAM Data Register 2004
reg oam_temp_wren;         // Write enable for OAM temp, disabled if full

// Extra Registers
reg [5:0] oam_addr_ex;     // OAM pointer for use with extra sprites
reg [3:0] oam_temp_slot_ex;
reg [1:0] m_ex;
reg [7:0] oam_data_ex;
reg [2:0] spr_counter;     // Count sprites

wire visible = (scanline < 240);
wire rendering = (scanline == 9'd511 || visible) && rendering_enabled;
wire evaluating = visible && rendering_enabled;

reg [5:0] oam_temp_addr;
reg [6:0] feed_cnt;

reg sprite0_curr;
reg [2:0] repeat_count;

assign masked_sprites = &repeat_count;

always @(posedge clk) begin :oam_eval
reg n_ovr, ex_ovr;
reg [1:0] eval_counter;
reg old_rendering;
reg [8:0] last_y, last_tile, last_attr;

reg overflow;

if (cycle == 340 && ce) begin
	sprite0 <= sprite0_curr;
	sprite0_curr <= 0;
end

if (reset) begin
	oam_temp <= '{64{8'hFF}};
	oam_data <= oam_temp[0];
	oam_temp_addr <= 0;
	oam_temp_slot <= 0;
	oam_temp_wren <= 1;
	oam_temp_slot_ex <= 0;
	n_ovr <= 0;
	spr_counter <= 0;
	repeat_count <= 0;
	sprite0 <= 0;
	sprite0_curr <= 0;
	feed_cnt <= 0;
	overflow <= 0;
	eval_counter <= 0;
	ex_ovr <= 0;
	oam_state <= STATE_IDLE;
end else if (ce) begin

	// State machine. Remember these will be one ppu cycle early.
	case (cycle)
		337: oam_state <= STATE_IDLE;    // 1 cycle
		338,0: oam_state <= STATE_CLEAR; // 64 cycles
		62:  oam_state <= STATE_EVAL;    // 192 cycles
		254: oam_state <= STATE_FETCH;   // 64 cycles
		318: oam_state <= STATE_REFRESH; // 19 cycles
	endcase

	// It is also the case that if OAMADDR is not less than eight when rendering starts,
	// the eight bytes starting at OAMADDR & 0xF8 are copied to the first eight bytes
	// of OAM
	if (rendering && cycle == 0) begin
		if (|oam_addr[7:3] && ~PAL) begin
			oam[0] <= oam[{oam_addr[7:3], 3'b000}];
			oam[1] <= oam[{oam_addr[7:3], 3'b001}];
			oam[2] <= oam[{oam_addr[7:3], 3'b010}];
			oam[3] <= oam[{oam_addr[7:3], 3'b011}];
			oam[4] <= oam[{oam_addr[7:3], 3'b100}];
			oam[5] <= oam[{oam_addr[7:3], 3'b101}];
			oam[6] <= oam[{oam_addr[7:3], 3'b110}];
			oam[7] <= oam[{oam_addr[7:3], 3'b111}];
		end
	end

	// XXX this is outside the "evaluating" block because of timing issues
	if (rendering) begin
		if (oam_state == STATE_IDLE) begin
			oam_data <= oam_temp[0];
			oam_temp_addr <= 0;
			oam_temp_slot <= 0;
			oam_temp_wren <= 1;
			oam_temp_slot_ex <= 0;
			oam_addr_ex <= 0;
			n_ovr <= 0;
			ex_ovr <= 0;
			spr_counter <= 0;
			repeat_count <= 0;
			feed_cnt <= 0;
			eval_counter <= 0;
			oam_bus_ex <= 32'hFFFFFFFF;
		end else if (oam_state == STATE_CLEAR) begin               // Initialization state
			oam_data <= 8'hFF;

			if (~cycle[0]) begin
				oam_temp[oam_temp_addr] <= 8'hFF;
				// Clear extra sprite space too
				oam_temp[oam_temp_addr + 6'd32] <= 8'hFF;
				oam_temp_addr <= oam_temp_addr + 1'b1;
			end

			// During init, we hunt for the 8th sprite in OAM, so we know where to start for extra sprites
			if (~&spr_counter) begin
				oam_addr_ex <= oam_addr_ex + 1'd1;
				if (scanline[7:0] >= oam[{oam_addr_ex, 2'b00}] && scanline[7:0] < oam[{oam_addr_ex, 2'b00}] + (obj_size ? 16 : 8))
					spr_counter <= spr_counter + 1'b1;
			end
		end else if (oam_state == STATE_EVAL) begin             // Evaluation State
			if (evaluating || (visible && PAL)) begin
				// This phase has exactly enough cycles to evaluate all 64 sprites if 8 are on the current line,
				// so extra sprite evaluation has to be done seperately.
				if (&spr_counter && ~ex_ovr) begin
					{ex_ovr, oam_addr_ex} <= oam_addr_ex + 7'd1;
					if (scanline[7:0] >= oam[{oam_addr_ex, 2'b00}] &&
						scanline[7:0] < oam[{oam_addr_ex, 2'b00}] + (obj_size ? 16 : 8)) begin
						if (oam_temp_slot_ex < 8) begin // Turbo style.
							oam_temp_slot_ex <= oam_temp_slot_ex + 1'b1;
							oam_temp[{oam_temp_slot_ex, 2'b00} + 6'd32] <= oam[{oam_addr_ex, 2'b00}];
							oam_temp[{oam_temp_slot_ex, 2'b01} + 6'd32] <= oam[{oam_addr_ex, 2'b01}];
							oam_temp[{oam_temp_slot_ex, 2'b10} + 6'd32] <= oam[{oam_addr_ex, 2'b10}];
							oam_temp[{oam_temp_slot_ex, 2'b11} + 6'd32] <= oam[{oam_addr_ex, 2'b11}];
						end
					end
				end

				//On odd cycles, data is read from (primary) OAM
				if (cycle[0]) begin
					oam_data <= oam[oam_addr];
				end else begin
					if (~n_ovr) begin
						if (oam_temp_wren)
							oam_temp[{1'b0, oam_temp_slot, oam_addr[1:0]}] <= oam_data;
						else
							oam_data <= oam_temp[{1'b0, oam_temp_slot, 2'b00}];
						if (~|eval_counter) begin // m is 0
							if (scanline[7:0] >= oam_data && scanline[7:0] < oam_data + (obj_size ? 16 : 8)) begin
								if (~oam_temp_wren)
									overflow <= 1;
								if (~|oam_addr[7:2])
									sprite0_curr <= 1'b1;
								eval_counter <= eval_counter + 2'd1;
								{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1; // is good, copy
							end else begin
								if (~oam_temp_wren) begin  // Sprite overflow bug emulation
									{n_ovr, oam_addr[7:2]} <= oam_addr[7:2] + 7'd1;
									oam_addr[1:0] <= oam_addr[1:0] + 2'd1;
								end else begin                              // skip to next sprite
									{n_ovr, oam_addr} <= oam_addr + 9'd4;
								end
							end
						end else begin
							eval_counter <= eval_counter + 2'd1;
							{n_ovr, oam_addr} <= {1'b0, oam_addr} + 9'd1;

							if (&eval_counter) begin // end of copy
								if (oam_temp_wren) begin
									last_y <= oam[{oam_addr[7:2], 2'b00}];
									last_tile <= oam[{oam_addr[7:2], 2'b01}];
									last_attr <= oam[{oam_addr[7:2], 2'b10}];
									// Check for repeats to see if the game is trying to mask sprites
									if (|oam_temp_slot &&
										last_y == oam[{oam_addr[7:2], 2'b00}] &&
										last_tile == oam[{oam_addr[7:2], 2'b01}] &&
										last_attr == oam[{oam_addr[7:2], 2'b10}]) begin
										repeat_count <= repeat_count + 3'd1;
									end
									oam_temp_slot <= oam_temp_slot+ 1'b1;
								end else begin
									n_ovr <= 1;
								end

								if (oam_temp_slot == 7)
									oam_temp_wren <= 0;
							end
						end
					end else begin
						oam_addr <= {oam_addr[7:2] + 1'd1, 2'b00};
						oam_data <= oam_temp[{1'b0, oam_temp_slot, 2'b00}];
					end
				end
				// Check if the 9th sprite is a repeat
				if (last_y    == oam_temp[6'd32] &&
					last_tile == oam_temp[6'd33] &&
					last_attr == oam_temp[6'd34] &&
					cycle == 9'h0FD && repeat_count < 7)
					repeat_count <= repeat_count + 3'd1;
			end
		end else if (oam_state == STATE_FETCH) begin
			feed_cnt <= feed_cnt + 1'd1;

			case (feed_cnt[2:0])
				0: begin // Y Coord
					oam_data <= oam_temp[{feed_cnt[6:3], 2'b00}];
					oam_bus_ex <= {
						oam_temp[{(feed_cnt[6:3] + 4'd8), 2'b11}],
						oam_temp[{(feed_cnt[6:3] + 4'd8), 2'b10}],
						oam_temp[{(feed_cnt[6:3] + 4'd8), 2'b01}],
						oam_temp[{(feed_cnt[6:3] + 4'd8), 2'b00}]
					};
				end

				1: begin // Tile Num
					oam_data <= oam_temp[{feed_cnt[6:3], 2'b01}];
				end

				2: begin // Attr
					oam_data <= oam_temp[{feed_cnt[6:3], 2'b10}];
				end

				3,4,5,6,7: begin // X Coord
					oam_data <= oam_temp[{feed_cnt[6:3], 2'b11}];
				end
			endcase
		end else begin // STATE_REFRESH
			oam_data <= oam_temp[0];
		end
	end else begin
		oam_data <= oam[oam_addr]; // Keep it available in case it's read
	end

	// OAMADDR is set to 0 during each of ticks 257-320 (the sprite tile loading interval) of the pre-render
	// and visible scanlines.
	if (oam_state == STATE_FETCH && rendering)
		oam_addr <= 0;

	// XXX: This delay is nessisary probably because the OAM handling is a cycle early
	spr_overflow <= overflow;

	if (is_vbe) begin
		overflow <= 0;
		spr_overflow <= 0;
	end

	// Writes to OAMDATA during rendering (on the pre-render line and the visible lines 0-239,
	// provided either sprite or background rendering is enabled) do not modify values in OAM,
	// but do perform a glitchy increment of OAMADDR, bumping only the high 6 bits (i.e., it bumps
	// the [n] value in PPU sprite evaluation - it's plausible that it could bump the low bits instead
	// depending on the current status of sprite evaluation). This extends to DMA transfers via OAMDMA,
	// since that uses writes to $2004. For emulation purposes, it is probably best to completely ignore
	// writes during rendering.
	if (oam_data_write) begin
		if (~rendering) begin
			oam[oam_addr] <= (oam_addr[1:0] == 2'b10) ? (oam_din & 8'hE3) : oam_din; // byte 3 has no bits 2-4
			oam_data <= (oam_addr[1:0] == 2'b10) ? (oam_din & 8'hE3) : oam_din;
			oam_addr <= oam_addr + 1'b1;
		end else begin
			oam_addr <= oam_addr + 8'd4;
		end
	end

	if (oam_addr_write) begin
		oam_addr <= oam_din;
	end

end
end // End Always

endmodule


// Generates addresses in VRAM where we'll fetch sprite graphics from,
// and populates load, load_in so the SpriteGen can be loaded.
// 10 LUT, 4 Slices
module SpriteAddressGen(
	input clk,
	input ce,
	input enabled,          // If unset, |load| will be all zeros.
	input obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input obj_patt,         // Object pattern table selection
	input [8:0] scanline,
	input [2:0] cycle,      // Current load cycle. At #4, first bitmap byte is loaded. At #6, second bitmap byte is.
	input [7:0] temp,       // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	input [7:0] vram_data,  // Byte of VRAM in the specified address
	output [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in   // Bits to load into SpritesGen.
);

reg [7:0] temp_tile;    // Holds the tile that we will get
reg [3:0] temp_y;       // Holds the Y coord (will be swapped based on FlipY).
reg flip_x, flip_y;     // If incoming bitmap data needs to be flipped in the X or Y direction.
wire load_y =    (cycle == 0);
wire load_tile = (cycle == 1);
wire load_attr = (cycle == 2) && enabled;
wire load_x =    (cycle == 3) && enabled;
wire load_pix1 = (cycle == 5) && enabled;
wire load_pix2 = (cycle == 7) && enabled;
reg dummy_sprite; // Set if attrib indicates the sprite is invalid.

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {vram_f, vram_f, temp, temp[1:0], temp[5]};

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.
assign vram_addr = {obj_size ? temp_tile[0] : obj_patt,
										temp_tile[7:1], obj_size ? y_f[3] : temp_tile[0], cycle[1], y_f[2:0] };
wire [7:0] scanline_y = scanline[7:0] - temp;
always @(posedge clk) if (ce) begin
	if (load_y) temp_y <= scanline_y[3:0];
	if (load_tile) temp_tile <= temp;
	if (load_attr) {flip_y, flip_x, dummy_sprite} <= {temp[7:6], temp[4]};
end

endmodule  // SpriteAddressGen


// Condensed sprite address generator for extra sprites
module SpriteAddressGenEx(
	input clk,
	input ce,
	input enabled,          // If unset, |load| will be all zeros.
	input obj_size,         // 0: Sprite Height 8, 1: Sprite Height 16.
	input obj_patt,         // Object pattern table selection
	input [7:0] scanline,
	input [2:0] cycle,      // Current load cycle. At #4, first bitmap byte is loaded. At #6, second bitmap byte is.
	input [31:0] temp,      // Input temp data from SpriteTemp. #0 = Y Coord, #1 = Tile, #2 = Attribs, #3 = X Coord
	input [7:0] vram_data,  // Byte of VRAM in the specified address
	output [12:0] vram_addr,// Low bits of address in VRAM that we'd like to read.
	output [3:0] load,      // Which subset of load_in that is now valid, will be loaded into SpritesGen.
	output [26:0] load_in,  // Bits to load into SpritesGen.
	output use_ex,          // If extra sprite address should be used
	input masked_sprites
);

// We keep an odd structure here to maintain compatibility with the existing sprite modules
// which are constrained by the behavior of the original system.
wire load_tile = (cycle == 1);
wire load_attr = (cycle == 2) && enabled;
wire load_x =    (cycle == 3) && enabled;
wire load_pix1 = (cycle == 5) && enabled;
wire load_pix2 = (cycle == 7) && enabled;

reg [7:0] pix1_latch, pix2_latch;

wire [7:0] temp_y = scanline[7:0] - temp[7:0];
wire [7:0] tile   = temp[15:8];
wire [7:0] attr   = temp[23:16];
wire [7:0] temp_x = temp[31:24];

wire flip_x = attr[6];
wire flip_y = attr[7];
wire dummy_sprite = attr[4];

assign use_ex = ~dummy_sprite && ~cycle[2] && ~masked_sprites;

// Flip incoming vram data based on flipx. Zero out the sprite if it's invalid. The bits are already flipped once.
wire [7:0] vram_f =
	dummy_sprite || masked_sprites ? 8'd0 :
	!flip_x ? {vram_data[0], vram_data[1], vram_data[2], vram_data[3], vram_data[4], vram_data[5], vram_data[6], vram_data[7]} :
	vram_data;

wire [3:0] y_f = temp_y[3:0] ^ {flip_y, flip_y, flip_y, flip_y};
assign load = {load_pix1, load_pix2, load_x, load_attr};
assign load_in = {pix1_latch, pix2_latch, load_temp, load_temp[1:0], load_temp[5]};

wire [7:0] load_temp;
always_comb begin
	case (cycle)
		0: load_temp = temp_y;
		1: load_temp = tile;
		2: load_temp = attr;
		3,4,5,6,7: load_temp = temp_x;
	endcase
end

// If $2000.5 = 0, the tile index data is used as usual, and $2000.3
// selects the pattern table to use. If $2000.5 = 1, the MSB of the range
// result value become the LSB of the indexed tile, and the LSB of the tile
// index value determines pattern table selection. The lower 3 bits of the
// range result value are always used as the fine vertical offset into the
// selected pattern.
assign vram_addr = {obj_size ? tile[0] : obj_patt,
										tile[7:1], obj_size ? y_f[3] : tile[0], cycle[1], y_f[2:0] };
always @(posedge clk) if (ce) begin
	if (load_tile) pix1_latch <= vram_f;
	if (load_x) pix2_latch <= vram_f;
end

endmodule  // SpriteAddressGen

module BgPainter(
	input clk,
	input ce,
	input enable,             // Shift registers activated
	input [2:0] cycle,
	input [2:0] fine_x_scroll,
	input [14:0] loopy,
	output [7:0] name_table,  // VRAM name table to read next.
	input [7:0] vram_data,
	output [3:0] pixel
);

reg [15:0] playfield_pipe_1;       // Name table pixel pipeline #1
reg [15:0] playfield_pipe_2;       // Name table pixel pipeline #2
reg [8:0]  playfield_pipe_3;       // Attribute table pixel pipe #1
reg [8:0]  playfield_pipe_4;       // Attribute table pixel pipe #2
reg [7:0] current_name_table;      // Holds the current name table byte
reg [1:0] current_attribute_table; // Holds the 2 current attribute table bits
reg [7:0] bg0;                     // Pixel data for last loaded background
wire [7:0] bg1 =  vram_data;

initial begin
	playfield_pipe_1 = 0;
	playfield_pipe_2 = 0;
	playfield_pipe_3 = 0;
	playfield_pipe_4 = 0;
	current_name_table = 0;
	current_attribute_table = 0;
	bg0 = 0;
end

always @(posedge clk) if (ce) begin
	case (cycle[2:0])
		1: current_name_table <= vram_data;
		3: current_attribute_table <=
			(!loopy[1] && !loopy[6]) ? vram_data[1:0] :
			( loopy[1] && !loopy[6]) ? vram_data[3:2] :
			(!loopy[1] &&  loopy[6]) ? vram_data[5:4] :
			vram_data[7:6];

		5: bg0 <= vram_data; // Pattern table bitmap #0
		//7: bg1 <= vram_data; // Pattern table bitmap #1
	endcase

	if (enable) begin
		playfield_pipe_1[14:0] <= playfield_pipe_1[15:1];
		playfield_pipe_2[14:0] <= playfield_pipe_2[15:1];
		playfield_pipe_3[7:0] <= playfield_pipe_3[8:1];
		playfield_pipe_4[7:0] <= playfield_pipe_4[8:1];
		// Load the new values into the shift registers at the last pixel.
		if (cycle[2:0] == 7) begin
			playfield_pipe_1[15:8] <= {bg0[0], bg0[1], bg0[2], bg0[3], bg0[4], bg0[5], bg0[6], bg0[7]};
			playfield_pipe_2[15:8] <= {bg1[0], bg1[1], bg1[2], bg1[3], bg1[4], bg1[5], bg1[6], bg1[7]};
			playfield_pipe_3[8] <= current_attribute_table[0];
			playfield_pipe_4[8] <= current_attribute_table[1];
		end
	end
end

assign name_table = current_name_table;

wire [3:0] i = {1'b0, fine_x_scroll};

assign pixel = {playfield_pipe_4[i], playfield_pipe_3[i], playfield_pipe_2[i], playfield_pipe_1[i]};

endmodule  // BgPainter


module PixelMuxer(
	input [3:0] bg,
	input [3:0] obj,
	input obj_prio,
	output [3:0] out,
	output is_obj
);

wire bg_flag = bg[0] | bg[1];
wire obj_flag = obj[0] | obj[1];

assign is_obj = !(obj_prio && bg_flag) && obj_flag;
assign out = is_obj ? obj : bg;

endmodule


module PaletteRam
(
	input clk,
	input ce,
	input [4:0] addr,
	input [5:0] din,
	output [5:0] dout,
	input write,
	input reset
);

reg [5:0] palette [32] = '{
	6'h00, 6'h01, 6'h00, 6'h01,
	6'h00, 6'h02, 6'h02, 6'h0D,
	6'h08, 6'h10, 6'h08, 6'h24,
	6'h00, 6'h00, 6'h04, 6'h2C,
	6'h09, 6'h01, 6'h34, 6'h03,
	6'h00, 6'h04, 6'h00, 6'h14,
	6'h08, 6'h3A, 6'h00, 6'h02,
	6'h00, 6'h20, 6'h2C, 6'h08
};

// Force read from backdrop channel if reading from any addr 0.
// Do this to the input, not here
//wire [4:0] addr2 = (addr[1:0] == 0) ? 5'd0 : addr;
// If 0x0,4,8,C: mirror every 0x10
wire [4:0] addr2 = (addr[1:0] == 0) ? {1'b0, addr[3:0]} : addr;
assign dout = palette[addr2];

always @(posedge clk) if (reset)
	palette <= '{
		6'h00, 6'h01, 6'h00, 6'h01,
		6'h00, 6'h02, 6'h02, 6'h0D,
		6'h08, 6'h10, 6'h08, 6'h24,
		6'h00, 6'h00, 6'h04, 6'h2C,
		6'h09, 6'h01, 6'h34, 6'h03,
		6'h00, 6'h04, 6'h00, 6'h14,
		6'h08, 6'h3A, 6'h00, 6'h02,
		6'h00, 6'h20, 6'h2C, 6'h08
	};
else if (ce && write) begin
	palette[addr2] <= din;
end

endmodule  // PaletteRam

module PPU(
	input         clk,
	input         ce,
	input         reset,            // input clock  21.48 MHz / 4. 1 clock cycle = 1 pixel
	inout   [1:0] sys_type,         // System type. 0 = NTSC 1 = PAL 2 = Dendy 3 = Vs.
	output  [5:0] color,            // output color value, one pixel outputted every clock
	input   [7:0] din,              // input data from bus
	output  [7:0] dout,             // output data to CPU
	input   [2:0] ain,              // input address from CPU
	input         read,             // read
	input         write,            // write
	input         read_raw,         // real read pin
	input         write_raw,        // real write pin
	output reg    nmi,              // one while inside vblank
	output        vram_r,           // read from vram active
	output        vram_r_ex,        // use extra sprite address
	output        vram_w,           // write to vram active
	output [13:0] vram_a,           // vram address
	output [13:0] vram_a_ex,        // vram address for extra sprites
	input   [7:0] vram_din,         // vram input
	output  [7:0] vram_dout,
	output  [8:0] scanline,
	output  [8:0] cycle,
	output [19:0] mapper_ppu_flags,
	output reg [2:0] emphasis,
	output       short_frame,
	input        extra_sprites,
	input  [1:0] mask
);

// These are stored in control register 0
reg obj_patt; // Object pattern table
reg bg_patt;  // Background pattern table
reg obj_size; // 1 if sprites are 16 pixels high, else 0.
reg vbl_enable;  // Enable VBL flag

// These are stored in control register 1
reg grayscale; // Disable color burst
reg playfield_clip;     // 0: Left side 8 pixels playfield clipping
reg object_clip;        // 0: Left side 8 pixels object clipping

initial begin
	obj_patt = 0;
	bg_patt = 0;
	obj_size = 0;
	vbl_enable = 0;
	grayscale = 0;
	playfield_clip = 0;
	object_clip = 0;
	enable_playfield = 0;
	enable_objects = 0;
	emphasis = 0;
end

reg nmi_occured;         // True if NMI has occured but not cleared.
reg [7:0] vram_latch;
//logic is_rendering;
// Clock generator
//wire is_in_vblank;        // True if we're in VBLANK
wire end_of_line;         // At the last pixel of a line
wire at_last_cycle_group; // At the very last cycle group of the scan line.
wire exiting_vblank;      // At the very last cycle of the vblank
wire entering_vblank;     //
wire is_pre_render_line;  // True while we're on the pre render scanline

reg enable_playfield, enable_objects;

wire rendering_enabled = enable_objects | enable_playfield;

// 2C02 has an "is_vblank" flag that is true from pixel 0 of line 241 to pixel 0 of line 0;
//wire is_rendering = rendering_enabled && (scanline < 240 || is_pre_render_line);
wire is_vbe_sl;


// The loopy module handles updating of the loopy address
wire [14:0] loopy;
wire [2:0] fine_x_scroll;

// Set to true if the current ppu_addr pointer points into palette ram.
wire is_pal_address = (loopy[13:8] == 6'b111111);

// Paints background
wire [7:0] bg_name_table;
wire [3:0] bg_pixel_noblank;

BgPainter bg_painter(
	.clk           (clk),
	.ce            (ce),
	.enable        (!at_last_cycle_group),
	.cycle         (cycle[2:0]),
	.fine_x_scroll (fine_x_scroll),
	.loopy         (loopy),
	.name_table    (bg_name_table),
	.vram_data     (vram_din),
	.pixel         (bg_pixel_noblank)
);

// Blank out BG in the leftmost 8 pixels?
wire show_bg_on_pixel = (playfield_clip || (cycle[7:3] != 0)) && enable_playfield;
wire [3:0] bg_pixel = {bg_pixel_noblank[3:2], show_bg_on_pixel ? bg_pixel_noblank[1:0] : 2'b00};

wire [31:0] oam_bus_ex;
wire masked_sprites;

OAMEval spriteeval (
	.clk               (clk),
	.ce                (ce),
	.reset             (reset),
	.rendering_enabled (rendering_enabled),
	.obj_size          (obj_size),
	.scanline          (scanline),
	.cycle             (cycle),
	.oam_bus           (oam_bus),
	.oam_bus_ex        (oam_bus_ex),
	.oam_addr_write    (write && (ain == 3)),
	.oam_data_write    (write && (ain == 4)),
	.oam_din           (din),
	.spr_overflow      (sprite_overflow),
	.sprite0           (obj0_on_line),
	.is_vbe            (clr_vbl_ovf_sp0),
	.PAL               (sys_type[0]),
	.masked_sprites    (masked_sprites)
);


wire [7:0] oam_bus;
wire sprite_overflow;
wire obj0_on_line; // True if sprite#0 is included on the current line

wire [4:0] obj_pixel_noblank;
wire [12:0] sprite_vram_addr;
wire is_obj0_pixel;            // True if obj_pixel originates from sprite0.
wire [3:0] spriteset_load;     // Which subset of the |load_in| to load into SpriteSet
wire [26:0] spriteset_load_in; // Bits to load into SpriteSet

// Between 256..319 (64 cycles), fetches bitmap data for the 8 sprites and fills in the SpriteSet
// so that it can start drawing on the next frame.
SpriteAddressGen address_gen(
	.clk       (clk),
	.ce        (ce),
	.enabled   (cycle[8] && !cycle[6]),  // Load sprites between 256..319
	.obj_size  (obj_size),
	.scanline  (scanline),
	.obj_patt  (obj_patt),               // Object size and pattern table
	.cycle     (cycle[2:0]),             // Cycle counter
	.temp      (is_pre_render_line || ~is_rendering ? 8'hFF : oam_bus),                // Info from temp buffer.
	.vram_addr (sprite_vram_addr),       // [out] VRAM Address that we want data from
	.vram_data (vram_din),               // [in] Data at the specified address
	.load      (spriteset_load),
	.load_in   (spriteset_load_in)       // Which parts of SpriteGen to load
);

wire [12:0] sprite_vram_addr_ex;
wire [3:0] spriteset_load_ex;
wire [26:0] spriteset_load_in_ex;
wire use_ex;

SpriteAddressGenEx address_gen_ex(
	.clk            (clk),
	.ce             (ce),
	.enabled        (cycle[8] && !cycle[6]),  // Load sprites between 256..319
	.obj_size       (obj_size),
	.scanline       (scanline[7:0]),
	.obj_patt       (obj_patt),               // Object size and pattern table
	.cycle          (cycle[2:0]),             // Cycle counter
	.temp           (is_pre_render_line || ~is_rendering ? 32'hFFFFFFFF : oam_bus_ex),                // Info from temp buffer.
	.vram_addr      (sprite_vram_addr_ex),    // [out] VRAM Address that we want data from
	.vram_data      (vram_din),               // [in] Data at the specified address
	.load           (spriteset_load_ex),
	.load_in        (spriteset_load_in_ex),    // Which parts of SpriteGen to load
	.use_ex         (use_ex),
	.masked_sprites (masked_sprites)
);

// Between 0..255 (256 cycles), draws pixels.
// Between 256..319 (64 cycles), will be populated for next line
SpriteSet sprite_gen(
	.clk           (clk),
	.ce            (ce),
	.enable        (!cycle[8]),
	.load          (spriteset_load),
	.load_in       (spriteset_load_in),
	.load_ex       (spriteset_load_ex),
	.load_in_ex    (spriteset_load_in_ex),
	.bits          (obj_pixel_noblank),
	.is_sprite0    (is_obj0_pixel),
	.extra_sprites (extra_sprites)
);

// Blank out obj in the leftmost 8 pixels?
wire show_obj_on_pixel = (object_clip || (cycle[7:3] != 0)) && enable_objects;
wire [4:0] obj_pixel = {obj_pixel_noblank[4:2], show_obj_on_pixel ? obj_pixel_noblank[1:0] : 2'b00};

reg sprite0_hit_bg;            // True if sprite#0 has collided with the BG in the last frame.
always @(posedge clk) if (ce) begin
	if (clr_vbl_ovf_sp0) begin
		sprite0_hit_bg <= 0;
	end else if (
		is_rendering        &&    // Object rendering is enabled
		!cycle[8]           &&    // X Pixel 0..255
		cycle[7:0] != 255   &&    // X pixel != 255
		!is_pre_render_line &&    // Y Pixel 0..239
		obj0_on_line        &&    // True if sprite#0 is included on the scan line.
		is_obj0_pixel       &&    // True if the pixel came from tempram #0.
		show_obj_on_pixel   &&
		bg_pixel[1:0] != 0) begin // Background pixel nonzero.

			sprite0_hit_bg <= 1;
	end
end

wire [3:0] pixel;
wire pixel_is_obj;

PixelMuxer pixel_muxer(
	.bg       (bg_pixel),
	.obj      (obj_pixel[3:0]),
	.obj_prio (obj_pixel[4]),
	.out      (pixel),
	.is_obj   (pixel_is_obj)
);

// VRAM Address Assignment

assign vram_a_ex = {1'b0, sprite_vram_addr_ex};

always_comb begin
	if (~is_rendering) begin
		vram_a = loopy[13:0];
		vram_r_ex = 0;
	end else begin
		// Extra sprite fetch override flag
		if (cycle[8] && !cycle[6])
			vram_r_ex = use_ex && extra_sprites;
		else
			vram_r_ex = 0;

		if (cycle[2:1] == 0)
			vram_a = {2'b10, loopy[11:0]};                                   // Name Table
		else if (cycle[2:1] == 1)
			vram_a = {2'b10, loopy[11:10], 4'b1111, loopy[9:7], loopy[4:2]}; // Attribute table
		else if (cycle[8] && !cycle[6])
			vram_a = {1'b0, sprite_vram_addr};                               // Sprite data
		else
			vram_a = {1'b0, bg_patt, bg_name_table, cycle[1], loopy[14:12]}; // Pattern table
	end
end

// Read from VRAM, either when user requested a manual read, or when we're generating pixels.
wire vram_r_ppudata = read && (ain == 7);

assign vram_r = vram_r_ppudata || is_rendering && cycle[0] == 0 && !end_of_line;

// Write to VRAM?
assign vram_w = write && (ain == 7) && !is_pal_address && !is_rendering;

wire [5:0] color2;
wire [4:0] pram_addr = is_rendering ?
	((|pixel[1:0]) ? {pixel_is_obj, pixel[3:0]} : 5'b00000) :
	(is_pal_address ? loopy[4:0] : 5'b0000);

PaletteRam palette_ram(
	.clk   (clk),
	.reset (reset),
	.ce    (ce),
	.addr  (pram_addr), // Read addr
	.din   (din[5:0]),  // Value to write
	.dout  (color2),    // Output color
	.write (write && (ain == 7) && is_pal_address) // Condition for writing
);

wire pal_mask = ~|scanline || cycle < 2 || cycle > 253;
wire auto_mask = (mask == 2'b11) && ~object_clip && ~playfield_clip;
wire mask_left = (cycle < 8) && ((|mask && ~&mask) || auto_mask);
wire mask_right = cycle > 247 && mask == 2'b10;
// PAL/Dendy masks scanline 0 and 2 pixels on each side with black.
wire mask_pal = (|sys_type && pal_mask);
wire [5:0] color1 = (grayscale ? {color2[5:4], 4'b0} : color2);
assign color = (mask_right | mask_left | mask_pal) ? 6'h0E : color1;

wire clear_nmi = (exiting_vblank | (read && ain == 2));
wire set_nmi = entering_vblank & ~clear_nmi;

logic pclk0;
logic pclk1;
logic held_reset;
logic is_visible;
logic clr_vbl_ovf_sp0;
//logic is_pre_render;
logic master_mode;
logic HVTog;


logic [7:0] delay_2001, latch_2001;
logic [7:0] delay_2000, latch_2000;
logic addr_inc;
logic read_old;
logic write_old;
logic read_ce;
logic write_ce;

always @(posedge clk) begin
	read_old <= read_raw;
	write_old <= write_raw;
end

assign write_ce = write_raw & ~write_old;
assign read_ce = read_raw & ~read_old;

// FIXME: move this logic to core's clock generators.
reg [1:0] ce2_cnt = 0;
wire CE2 = ce2_cnt == 1;
always_ff @(posedge clk) begin
	if (ce2_cnt) ce2_cnt <= ce2_cnt - 1'd1;
	if (ce) ce2_cnt <= 2;
end

// assign pclk0 = ce;
// assign pclk1 = CE2;
logic is_rendering;

// ClockGen clock(
// 	.clk                 (clk),
// 	.ce                  (ce),
// 	.reset               (reset),
// 	.sys_type            (sys_type),
// 	.is_rendering        (rendering_enabled),
// 	.scanline            (scanline),
// 	.cycle               (cycle),
// 	.is_in_vblank        (is_in_vblank),
// 	.end_of_line         (end_of_line),
// 	.at_last_cycle_group (at_last_cycle_group),
// 	.exiting_vblank      (exiting_vblank),
// 	.entering_vblank     (entering_vblank),
// 	.is_pre_render       (is_pre_render_line),
// 	.short_frame         (short_frame),
// 	.is_vbe_sl           (is_vbe_sl)
// );


ClockGen clock(
	.clk                 (clk),
	.ce                  (ce),
	.ce2                 (CE2),
	.reset               (reset),
	.held_reset          (held_reset),
	.sys_type            (sys_type),
	.rendering_enabled   (rendering_enabled),
	.scanline            (scanline),
	.cycle               (cycle),
	.end_of_line         (end_of_line),
	.at_last_cycle_group (at_last_cycle_group),
	.exiting_vblank      (exiting_vblank),
	.entering_vblank     (entering_vblank),
	.is_pre_render       (is_pre_render_line),
	.is_visible          (is_visible),
	.is_rendering        (is_rendering),
	.short_frame         (short_frame),
	.clr_vbl_ovf_sp0     (clr_vbl_ovf_sp0),
	.pclk0               (pclk0),
	.pclk1               (pclk1),
	.is_vbe_sl           (is_vbe_sl) //FIXME: Deprecated, switch to clr_vbl_ovf_sp0
);

VramGen vram_v0(
	.clk                 (clk),
	.reset               (reset),
	.ce                  (pclk0),
	.pclk1               (pclk1),
	.ppu_incr            (addr_inc),
	.read_ce             (read_ce),
	.write_ce            (write_ce),
	.is_rendering        (is_rendering),
	.rendering_enabled   (rendering_enabled),
	.ain                 (ain),
	.din                 (din),
	.read                (read_raw),
	.write               (write_raw),
	.is_pre_render       (is_pre_render_line),
	.cycle               (cycle),
	.HVTog               (HVTog),
	.vram_v              (loopy),
	.fine_x_scroll       (fine_x_scroll)
);

// After spending a few sultry afternoons with visual 2c02, it seems that writes to the PPU follow a
// pattern most of the time. Read and Write are almost always goverened by three inputs: The cpu's
// read-or-write signal, the CE signal (called CS here) which is defined as phi2 AND the cpu address
// is in ppu range, and lastly by the lowest three bits of the address bus itself. In practice what
// this means is that when (write & phi2) are true, the CPU latches to an internal register, but the
// rest of the chip doesn't see this yet. When phi2 goes low, finally the chip reconnects the
// latching register to the internal wires and the effects of the writes take effect. The exceptions
// to this are Enable NMI, Slave Mode, and Grayscale which appear run wires directly to the latching
// register, and thus take effect as soon as (write & ce) are true. HVTog, 2006 and 2005 writes seem
// to behave the same as described above.

// These three signals tap directly into the latch register and apply instantly
assign vbl_enable = write_raw && ain == 0 ? din[7] : delay_2000[7];
//assign master_mode = write_raw && ain == 0 ? din[6] : delay_2000[6]; // In case it's ever needed
assign grayscale = write_raw && ain == 1 ? din[0] : delay_2001[0];

// 2000 Latched data, only applies after the write signal goes low
assign addr_inc = ~write_raw ? delay_2000[2] : latch_2000[2];
assign obj_patt = ~write_raw ? delay_2000[3] : latch_2000[3];
assign bg_patt = ~write_raw ? delay_2000[4] : latch_2000[4];
assign obj_size = ~write_raw ? delay_2000[5] : latch_2000[5];

// 2001 Latched data, only applies after the write signal goes low
assign playfield_clip = ~write_raw ? delay_2001[1] : latch_2001[1];
assign object_clip = ~write_raw ? delay_2001[2] : latch_2001[2];
assign enable_playfield = ~write_raw ? delay_2001[3] : latch_2001[3];
assign enable_objects = ~write_raw ? delay_2001[4] : latch_2001[4];

assign emphasis[1:0] = ~write_raw ?
	(|sys_type ? {delay_2001[5], delay_2001[6]} : delay_2001[6:5]) :
	(|sys_type ? {latch_2001[5], latch_2001[6]} : latch_2001[6:5]);
assign emphasis[2] = write_raw && ain == 1 ? din[7] : delay_2001[7];


logic hv_latch;

always @(posedge clk) begin
	if (reset) begin
		//vbl_flag <= 0;
		delay_2000 <= 8'd0;
		delay_2001 <= 8'd0;
		latch_2000 <= 8'd0;
		latch_2001 <= 8'd0;
		HVTog <= 0;
		hv_latch <= 0;
	end else begin
		if (read_raw && ain == 2)
			hv_latch <= 0;

		if (write_raw) begin
			case (ain)
				0: begin // PPU Control Register 1
					delay_2000 <= din;
				end

				1: begin // PPU Control Register 2
					delay_2001 <= din;
				end

				5, 6: hv_latch <= ~HVTog;
			endcase
		end else begin
			HVTog <= hv_latch;
			latch_2000 <= delay_2000;
			latch_2001 <= delay_2001;
		end
	end

	// if (pclk0) begin
	// 	if (exiting_vblank)
	// 		vbl_flag <= 0;
	// 	else if (entering_vblank)
	// 		vbl_flag <= 1;
	// end

	// if (read && AIN == 2)
	// 	vbl_flag <= 0;
end

always @(posedge clk)
if (ce) begin
	if (reset) begin
	// 	{obj_patt, bg_patt, obj_size, vbl_enable} <= 0; // 2000 resets to 0
	// 	{grayscale, playfield_clip, object_clip, enable_playfield, enable_objects, emphasis} <= 0; // 2001 resets to 0
		nmi_occured <= 0;
	end //else if (write) begin
	// 	case (ain)
	// 		0: begin // PPU Control Register 1
	// 			// t:....BA.. ........ = d:......BA
	// 			obj_patt <= din[3];
	// 			bg_patt <= din[4];
	// 			obj_size <= din[5];
	// 			vbl_enable <= din[7];
	// 		end

	// 		1: begin // PPU Control Register 2
	// 			grayscale <= din[0];
	// 			playfield_clip <= din[1];
	// 			object_clip <= din[2];
	// 			enable_playfield <= din[3];
	// 			enable_objects <= din[4];
	// 			emphasis <= |sys_type ? {din[7], din[5], din[6]} : din[7:5];
	// 		end
	// 	endcase
	// end
	// https://wiki.nesdev.com/w/index.php/NMI
	if (set_nmi)
		nmi_occured <= 1;
	if (clear_nmi)
		nmi_occured <= 0;
end

// If we're triggering a VBLANK NMI
assign nmi = nmi_occured && vbl_enable;


// One cycle after vram_r was asserted, the value
// is available on the bus.
reg vram_read_delayed;
always @(posedge clk) if (ce) begin
	if (vram_read_delayed)
		vram_latch <= vram_din;
	vram_read_delayed <= vram_r_ppudata;
end

// Value currently being written to video ram
assign vram_dout = din;

// Last data on bus is persistent
reg [7:0] latched_dout;

reg [23:0] decay_high;
reg [23:0] decay_low;

reg refresh_high, refresh_low;

always @(posedge clk) begin
	if (refresh_high) begin
		decay_high <= 3221590; // aprox 600ms decay rate
		refresh_high <= 0;
	end

	if (refresh_low) begin
		decay_low <= 3221590;
		refresh_low <= 0;
	end

	if (ce) begin
		if (decay_high > 0)
			decay_high <= decay_high - 1'b1;
		else
			latched_dout[7:5] <= 3'b000;

		if (decay_low > 0)
			decay_low <= decay_low - 1'b1;
		else
			latched_dout[4:0] <= 5'b00000;
	end

	if (read) begin
		case (ain)
			2: begin
				latched_dout <= {nmi_occured,
								sprite0_hit_bg,
								sprite_overflow,
								latched_dout[4:0]};
				refresh_high <= 1'b1;
			end

			4: begin
				latched_dout <= oam_bus;
				refresh_high <= 1'b1;
				refresh_low <= 1'b1;
			end

			7: if (is_pal_address) begin
					latched_dout <= {latched_dout[7:6], color1};
					refresh_low <= 1'b1;
				end else begin
					latched_dout <= vram_latch;
					refresh_high <= 1'b1;
					refresh_low <= 1'b1;
				end
			default: latched_dout <= latched_dout;
		endcase

		if (reset)
			latched_dout <= 8'd0;

	end else if (write) begin
		refresh_high <= 1'b1;
		refresh_low <= 1'b1;
		latched_dout <= din;
	end
end

assign dout = latched_dout;


assign mapper_ppu_flags = {scanline, cycle, obj_size, is_rendering};

endmodule  // PPU