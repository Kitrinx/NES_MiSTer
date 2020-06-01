// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

module DelayWrite (
	input logic clk,
	input logic gate,
	input logic reset,
	input logic [WIDTH-1'd1:0] din,
	output logic [WIDTH-1'd1:0] dout
);
	parameter WIDTH = 8;

	logic [WIDTH-1'd1:0] din_latch;

	always_ff @(posedge clk)
		if (reset)
			din_latch <= 0;
		else if (gate)
			din_latch <= din;

	assign dout = gate ? din : din_latch;

endmodule

module LenCounterUnit (
	input  logic       clk,
	input  logic       reset,
	input  logic       cold_reset,
	input  logic       len_clk,
	input  logic       aclk1,
	input  logic [4:0] load_value,
	input  logic       halt_in,
	input  logic       addr,
	input  logic       is_triangle,
	input  logic       write,
	input  logic       enabled,
	output logic [7:0] length_counter
);

	logic [6:0] len_counter_lut[32];
	assign len_counter_lut = '{
		7'h05, 7'h7F, 7'h0A, 7'h01,
		7'h14, 7'h02, 7'h28, 7'h03,
		7'h50, 7'h04, 7'h1E, 7'h05,
		7'h07, 7'h06, 7'h0D, 7'h07,
		7'h06, 7'h08, 7'h0C, 7'h09,
		7'h18, 7'h0A, 7'h30, 7'h0B,
		7'h60, 7'h0C, 7'h24, 7'h0D,
		7'h08, 7'h0E, 7'h10, 7'h0F
	};

	logic [7:0] len_counter_int;

	assign length_counter = enabled ? len_counter_int : 7'd0;

	always_ff @(posedge clk) begin : lenunit
		logic halt, halt_next, halt_reload;
		logic [7:0] len_counter_next;
		logic len_reload;

		if (aclk1) begin
			if (len_reload) len_counter_int <= len_counter_next;
			if (halt_reload) halt <= halt_next;

			halt_reload <= 0;
			len_reload <= 0;
		end

		if (write) begin
			if (~addr) begin
				halt_reload <= 1;
				halt_next <= halt_in;
			end else if (enabled) begin
				len_reload <= 1;
				len_counter_next <= {len_counter_lut[load_value], 1'b0};
			end
		end

		// This deliberately can overwrite being loaded from writes
		if (len_clk && enabled && |len_counter_int && ~halt) begin
			len_reload <= 0;
			len_counter_int <= len_counter_int - 1'd1;
		end

		if (~enabled) begin
			len_counter_int <= 0;
			len_counter_next <= 0;
			len_reload <= 0;
		end

		if (reset) begin
			if (~is_triangle || cold_reset) begin
				halt <= 0;
				halt_next <= 0;
				halt_reload <= 0;
			end
			len_counter_int <= 0;
			len_reload <= 0;
			len_counter_next <= 0;
		end
	end

endmodule

module EnvelopeUnit (
	input  logic       clk,
	input  logic       reset,
	input  logic       env_clk,
	input  logic [5:0] din,
	input  logic       addr,
	input  logic       write,
	output logic [3:0] envelope
);

	logic [3:0] env_count, env_vol;
	logic env_disabled;

	assign envelope = env_disabled ? env_vol : env_count;

	always_ff @(posedge clk) begin : envunit
		logic [3:0] env_div;
		logic env_reload;
		logic env_loop;
		logic env_reset;

		if (env_clk) begin
			if (~env_reload) begin
				env_div <= env_div - 1'd1;
				if (~|env_div) begin
					env_div <= env_vol;
					if (|env_count || env_loop)
						env_count <= env_count - 1'd1;
				end
			end else begin
				env_div <= env_vol;
				env_count <= 4'hF;
				env_reload <= 1'b0;
			end
		end

		if (write) begin
			if (~addr) {env_loop, env_disabled, env_vol} <= din;
			if (addr) env_reload <= 1;
		end

		if (reset) begin
			env_loop <= 0;
			env_div <= 0;
			env_vol <= 0;
			env_count <= 0;
			env_reload <= 0;
		end
	end

endmodule

module SquareChan (
	input  logic       MMC5,
	input  logic       clk,
	input  logic       ce,
	input  logic       aclk1,
	input  logic       reset,
	input  logic       cold_reset,
	input  logic       sq2,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       write,
	input  logic       LenCtr_Clock,
	input  logic       Env_Clock,
	input  logic       odd_or_even,
	input  logic       Enabled,
	output logic [3:0] Sample,
	output logic       IsNonZero
);

	// Register 1
	logic [1:0] Duty;

	// Register 2
	logic SweepEnable, SweepNegate, SweepReset;
	logic [2:0] SweepPeriod, SweepDivider, SweepShift;

	logic [10:0] Period;
	logic [11:0] TimerCtr;
	logic [2:0] SeqPos;
	logic [10:0] ShiftedPeriod;
	logic [10:0] PeriodRhs;
	logic [11:0] NewSweepPeriod;

	logic ValidFreq;
	logic subunit_write;
	logic [3:0] Envelope;
	logic [7:0] LenCtr;

	assign ShiftedPeriod = (Period >> SweepShift);
	assign PeriodRhs = (SweepNegate ? (~ShiftedPeriod + {10'b0, sq2}) : ShiftedPeriod);
	assign NewSweepPeriod = Period + PeriodRhs;
	assign subunit_write = (Addr == 0 || Addr == 3) & write;
	assign IsNonZero = (LenCtr != 0);

	// NOTE: This should be always be enabled for MMC5, but do we really want ultrasonic frequencies?
	assign ValidFreq = /*(MMC5==1) ||*/ ((|Period[10:3]) && (SweepNegate || !NewSweepPeriod[11]));
	assign Sample = (~|LenCtr | ~ValidFreq | ~DutyEnabledUsed | ~|TimerCtr[2:0]) ? 4'd0 : Envelope;

	LenCounterUnit LenSq (
		.clk            (clk),
		.reset          (reset),
		.cold_reset     (cold_reset),
		.aclk1          (aclk1),
		.len_clk        (MMC5 ? Env_Clock : LenCtr_Clock),
		.load_value     (DIN[7:3]),
		.halt_in        (DIN[5]),
		.addr           (Addr[0]),
		.is_triangle    (1'b0),
		.write          (subunit_write),
		.enabled        (Enabled),
		.length_counter (LenCtr)
	);

	EnvelopeUnit EnvSq (
		.clk            (clk),
		.reset          (reset),
		.env_clk        (Env_Clock),
		.din            (DIN[5:0]),
		.addr           (Addr[0]),
		.write          (subunit_write),
		.envelope       (Envelope)
	);

	always_ff @(posedge clk) begin
		if (aclk1) begin
			if (TimerCtr == 0) begin
				// Timer was clocked
				TimerCtr <= Period;
				SeqPos <= SeqPos - 1'd1;
			end else begin
				TimerCtr <= TimerCtr - 1'd1;
			end
		end

		// Sweep Unit
		if (LenCtr_Clock) begin
			if (SweepDivider == 0) begin
				SweepDivider <= SweepPeriod;
				if (SweepEnable && SweepShift != 0 && ValidFreq)
					Period <= NewSweepPeriod[10:0];
			end else begin
				SweepDivider <= SweepDivider - 1'd1;
			end
			if (SweepReset)
				SweepDivider <= SweepPeriod;
			SweepReset <= 0;
		end

		if (write) begin
			case (Addr)
				0: Duty <= DIN[7:6];
				1: if (~MMC5) begin
					{SweepEnable, SweepPeriod, SweepNegate, SweepShift} <= DIN;
					SweepReset <= 1;
				end
				2: Period[7:0] <= DIN;
				3:begin
					Period[10:8] <= DIN[2:0];
					SeqPos <= 0;
				end
			endcase
		end

		if (reset) begin
			Duty <= 0;
			SweepEnable <= 0;
			SweepNegate <= 0;
			SweepReset <= 0;
			SweepPeriod <= 0;
			SweepDivider <= 0;
			SweepShift <= 0;
			Period <= 0;
			TimerCtr <= 0;
			SeqPos <= 0;
		end
	end

	logic DutyEnabledUsed;
	assign DutyEnabledUsed = MMC5 ^ DutyEnabled;

	logic DutyEnabled;
	always_comb begin
		// Determine if the duty is enabled or not
		case (Duty)
			0: DutyEnabled = (SeqPos == 7);
			1: DutyEnabled = (SeqPos >= 6);
			2: DutyEnabled = (SeqPos >= 4);
			3: DutyEnabled = (SeqPos < 6);
		endcase
	end

endmodule

module TriangleChan (
	input  logic       clk,
	input  logic       phi1,
	input  logic       aclk1,
	input  logic       reset,
	input  logic       cold_reset,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       MW,
	input  logic       LenCtr_Clock,
	input  logic       LinCtr_Clock,
	input  logic       Enabled,
	output logic [3:0] Sample,
	output logic       IsNonZero
);
	logic [10:0] Period, TimerCtr;
	logic [4:0] SeqPos;
	logic [6:0] LinCtrPeriod, LinCtr;
	logic LinCtrl, line_reload;
	logic LinCtrZero;

	logic [7:0] LenCtr;
	logic LenCtrZero;
	logic subunit_write;
	logic [3:0] sample_latch;
	logic line_reload_2;
	logic line_control_2;

	assign LinCtrZero = ~|LinCtr;
	assign LenCtrZero = ~|LenCtr;
	assign IsNonZero = ~LenCtrZero;
	assign subunit_write = (Addr == 0 || Addr == 3) & MW;

	LenCounterUnit LenSq (
		.clk            (clk),
		.reset          (reset),
		.cold_reset     (cold_reset),
		.aclk1          (aclk1),
		.len_clk        (LenCtr_Clock),
		.load_value     (DIN[7:3]),
		.halt_in        (DIN[7]),
		.addr           (Addr[0]),
		.is_triangle    (1'b1),
		.write          (subunit_write),
		.enabled        (Enabled),
		.length_counter (LenCtr)
	);

	always_ff @(posedge clk) begin
		if (phi1) begin
			if (TimerCtr == 0) begin
				TimerCtr <= Period;
				if (IsNonZero & ~LinCtrZero)
					SeqPos <= SeqPos + 1'd1;
			end else begin
				TimerCtr <= TimerCtr - 1'd1;
			end
		end

		if (LinCtr_Clock) begin
			if (line_reload_2)
				LinCtr <= LinCtrPeriod;
			else if (!LinCtrZero)
				LinCtr <= LinCtr - 1'd1;

			if (!line_control_2)
				line_reload <= 0;
		end

		if (aclk1) begin
			line_reload_2 <= line_reload;
			line_control_2 <= LinCtrl;
		end

		if (MW) begin
			case (Addr)
				0: begin
					LinCtrl <= DIN[7];
					LinCtrPeriod <= DIN[6:0];
				end
				2: begin
					Period[7:0] <= DIN;
				end
				3: begin
					Period[10:8] <= DIN[2:0];
					line_reload <= 1;
				end
			endcase
		end

		if (reset) begin
			sample_latch <= 4'hF;
			Period <= 0;
			TimerCtr <= 0;
			SeqPos <= 0;
			LinCtrPeriod <= 0;
			LinCtr <= 0;
			LinCtrl <= 0;
			line_reload <= 0;
		end

		if (Period > 1) sample_latch <= Sample;
	end

	// XXX: Ultrisonic frequencies cause issues, so are disabled.
	// This can be removed for accuracy if a proper LPF is ever implemented.
	assign Sample = (Period > 1) ? SeqPos[3:0] ^ {4{~SeqPos[4]}} : sample_latch;

endmodule

module NoiseChan (
	input  logic       clk,
	input  logic       ce,
	input  logic       aclk1,
	input  logic       aclk1_d,
	input  logic       reset,
	input  logic       cold_reset,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       PAL,
	input  logic       MW,
	input  logic       LenCtr_Clock,
	input  logic       Env_Clock,
	input  logic       Enabled,
	output logic [3:0] Sample,
	output logic       IsNonZero
);
	logic ShortMode;
	logic [14:0] Shift;
	logic [3:0] Period;
	logic [11:0] NoisePeriod, TimerCtr;
	logic [7:0] LenCtr;
	logic [3:0] Envelope;
	logic subunit_write;

	assign IsNonZero = (LenCtr != 0);
	assign subunit_write = (Addr == 0 || Addr == 3) & MW;

	// Produce the output signal
	assign Sample = (~|LenCtr || Shift[14]) ? 4'd0 : Envelope;

	LenCounterUnit LenSq (
		.clk            (clk),
		.reset          (reset),
		.cold_reset     (cold_reset),
		.aclk1          (aclk1),
		.len_clk        (LenCtr_Clock),
		.load_value     (DIN[7:3]),
		.halt_in        (DIN[5]),
		.addr           (Addr[0]),
		.is_triangle    (1'b0),
		.write          (subunit_write),
		.enabled        (Enabled),
		.length_counter (LenCtr)
	);

	EnvelopeUnit EnvSq (
		.clk            (clk),
		.reset          (reset),
		.env_clk        (Env_Clock),
		.din            (DIN[5:0]),
		.addr           (Addr[0]),
		.write          (subunit_write),
		.envelope       (Envelope)
	);

	logic [10:0] noise_pal_lut[16];
	assign noise_pal_lut = '{
		11'h200, 11'h280, 11'h550, 11'h5D5,
		11'h393, 11'h74F, 11'h61B, 11'h41F,
		11'h661, 11'h1C5, 11'h6AE, 11'h093,
		11'h4FE, 11'h12D, 11'h679, 11'h392
	};

	// Values read directly from the netlist
	logic [10:0] noise_ntsc_lut[16];
	assign noise_ntsc_lut = '{
		11'h200, 11'h280, 11'h2A8, 11'h6EA,
		11'h4E4, 11'h674, 11'h630, 11'h730,
		11'h4AC, 11'h304, 11'h722, 11'h230,
		11'h213, 11'h782, 11'h006, 11'h014
	};

	logic [10:0] noise_timer;
	always_ff @(posedge clk) begin
		// Things we know.
		// They clock and reset together at aclk1_d
		// The output of shift14 is gated by aclk1
		// The output of shift10 is gated by aclk1
		// The output of shift 14 is a put through a nor gate with itself and silence flags to final.

		// These are reloaded with the next value at aclk1_d and the values are presented at aclk1
		if (aclk1) begin
			noise_timer <= {noise_timer[9:0], (noise_timer[10] ^ noise_timer[8]) | ~|noise_timer};

			if (noise_timer == 'h400) begin
				noise_timer <= PAL ? noise_pal_lut[Period] : noise_ntsc_lut[Period];
				Shift <= {Shift[13:0], ((Shift[14] ^ (ShortMode ? Shift[8] : Shift[13])) | ~|Shift)};
			end
		end

		if (MW && Addr == 2) begin
			ShortMode <= DIN[7];
			Period <= DIN[3:0];
		end

		if (reset) begin
			noise_timer <= cold_reset ? 11'd0 : (PAL ? noise_pal_lut[0] : noise_ntsc_lut[0]);
			ShortMode <= 0;
			Shift <= 0;
			Period <= 0;
		end
	end
endmodule

module DmcChan (
	input  logic        MMC5,
	input  logic        clk,
	input  logic        ce,
	input  logic        aclk1,
	input  logic        reset,
	input  logic        cold_reset,
	input  logic        odd_or_even,
	input  logic  [2:0] Addr,
	input  logic  [7:0] DIN,
	input  logic        MW,
	input  logic        DmaAck,      // 1 when DMC byte is on DmcData. DmcDmaRequested should go low.
	input  logic  [7:0] DmaData,     // Input data to DMC from memory.
	input  logic        PAL,
	output logic [15:0] DmaAddr,     // Address DMC wants to read
	output logic        Irq,
	output logic  [6:0] Sample,
	output logic        DmaReq,      // 1 when DMC wants DMA
	output logic        IsDmcActive
);
	logic IrqEnable;
	logic IrqActive;
	logic Loop;                 // Looping enabled
	logic [3:0] Freq;           // Current value of frequency register
	logic [7:0] Dac;        // Current value of DAC
	logic [14:0] SampleAddress;  // Base address of sample
	logic [7:0] SampleLen;      // Length of sample
	logic [7:0] ShiftReg;       // Shift register
	logic [8:0] Cycles;         // Down counter, is the period
	logic [14:0] Address;        // 15 bits current address, 0x8000-0xffff
	logic [11:0] BytesLeft;      // 12 bits bytes left counter 0 - 4081.
	logic [2:0] BitsUsed;        // Number of bits left in the SampleBuffer.
	logic [7:0] SampleBuffer;    // Next value to be loaded into shift reg
	logic HasSampleBuffer;       // Sample buffer is nonempty
	logic HasShiftReg;           // Shift reg is non empty
	logic DmcEnabled;
	logic [1:0] ActivationDelay;

	assign DmaAddr = {1'b1, Address};
	assign Sample = Dac[6:0];
	assign Irq = IrqActive;
	assign IsDmcActive = DmcEnabled;

	assign DmaReq = !HasSampleBuffer && DmcEnabled && !ActivationDelay[0];

	logic [8:0] NewPeriod[16];
	assign NewPeriod = '{
		9'd428, 9'd380, 9'd340, 9'd320,
		9'd286, 9'd254, 9'd226, 9'd214,
		9'd190, 9'd160, 9'd142, 9'd128,
		9'd106, 9'd84,  9'd72,  9'd54
	};

	logic [8:0] NewPeriodPAL[16];
	assign NewPeriodPAL = '{
		9'd398, 9'd354, 9'd316, 9'd298,
		9'd276, 9'd236, 9'd210, 9'd198,
		9'd176, 9'd148, 9'd132, 9'd118,
		9'd98,  9'd78,  9'd66,  9'd50
	};

	logic [7:0] dac_delay;
	logic load_dac;

	// Shift register initially loaded with 07
	always_ff @(posedge clk) begin
		if (MW) begin
			case (Addr)
			0: begin  // $4010 // Applies at aclk1.
					IrqEnable <= DIN[7];
					Loop <= DIN[6];
					Freq <= DIN[3:0];
					if (!DIN[7]) IrqActive <= 0;
				end
			1: begin  // $4011 Applies at aclk1
					// This will get missed if the Dac <= far below runs, that is by design.
					load_dac <= 1;
					dac_delay <= {MMC5 & DIN[7], DIN[6:0]};
				end
			2: begin  // $4012 applies immediately
					SampleAddress <= MMC5 ? 15'h00 : {1'b1, DIN[7:0], 6'b000000};
				end
			3: begin  // $4013 applies immediately
					SampleLen <= (MMC5==1) ? 8'h0 : DIN[7:0];
				end
			5: begin // $4015 write	---D NT21  Enable DMC (D)
					IrqActive <= 0; // Applies immediately
					DmcEnabled <= DIN[4]; // Applies at aclk1
					// If the DMC bit is set, the DMC sample will be restarted only if not already active.
					if (~DIN[4])
						BytesLeft <= 0;

					if (DIN[4] && ~|BytesLeft) begin
						Address <= SampleAddress;
						BytesLeft <= {SampleLen, 4'b0000};
						ActivationDelay <= 2'd3;
					end
				end
			endcase
		end

		if (aclk1) begin
			load_dac <= 0;
			if (load_dac)
				Dac <= dac_delay;
		end

		if (ce) begin
			if (ActivationDelay == 3 && !odd_or_even) ActivationDelay <= 1; // aclk1_d
			if (ActivationDelay == 1) ActivationDelay <= 0; // Aclk1

			Cycles <= Cycles - 1'd1;
			if (Cycles == 1) begin
				Cycles <= PAL ? NewPeriodPAL[Freq] : NewPeriod[Freq];
				if (HasShiftReg) begin
					if (ShiftReg[0]) begin
						Dac[6:1] <= (Dac[6:1] != 6'b111111) ? Dac[6:1] + 6'b000001 : Dac[6:1];
					end else begin
						Dac[6:1] <= (Dac[6:1] != 6'b000000) ? Dac[6:1] + 6'b111111 : Dac[6:1];
					end
				end
				ShiftReg <= {1'b0, ShiftReg[7:1]};
				BitsUsed <= BitsUsed + 1'd1;
				if (BitsUsed == 7) begin
					HasShiftReg <= HasSampleBuffer;
					ShiftReg <= SampleBuffer;
					HasSampleBuffer <= 0;
				end
			end

			// Acknowledge DMA?
			if (DmaAck) begin
				Address <= Address + 1'd1;
				BytesLeft <= BytesLeft - 1'd1;
				HasSampleBuffer <= 1;
				SampleBuffer <= DmaData;
				if (BytesLeft == 0) begin
					Address <= SampleAddress;
					BytesLeft <= {SampleLen, 4'b0000};
					DmcEnabled <= Loop;
					if (!Loop && IrqEnable)
						IrqActive <= 1;
				end
			end
		end

		if (reset) begin
			IrqEnable <= 0;
			IrqActive <= 0;
			Loop <= 0;
			Freq <= 0;
			Dac <= 0;
			ShiftReg <= 8'h0;
			Cycles <= 439;
			BytesLeft <= 0;
			BitsUsed <= 0;
			SampleBuffer <= 0;
			HasSampleBuffer <= 0;
			HasShiftReg <= 0;
			DmcEnabled <= 0;
			ActivationDelay <= 0;
		end

		if (cold_reset) begin
			SampleAddress <= 15'h0000;
			SampleLen <= 1;
			Address <= 15'h0000;
		end
	end

endmodule


module DmcChan2 (
	input  logic        MMC5,
	input  logic        clk,
	input  logic        phi1,
	input  logic        aclk1,
	input  logic        aclk1_d,
	input  logic        reset,
	input  logic        cold_reset,
	input  logic  [2:0] ain,
	input  logic  [7:0] DIN,
	input  logic        write_ce,
	input  logic        write,
	input  logic        dma_ack,      // 1 when DMC byte is on DmcData. DmcDmaRequested should go low.
	input  logic  [7:0] dma_data,     // Input data to DMC from memory.
	input  logic        PAL,
	output logic [15:0] dma_address,     // Address DMC wants to read
	output logic        irq,
	output logic  [6:0] Sample,
	output logic        dma_req,      // 1 when DMC wants DMA
	output logic        enable
);
	logic irq_enable;
	logic loop;                 // Looping enabled
	logic [3:0] frequency;           // Current value of frequency register
	logic [14:0] sample_address;  // Base address of sample
	logic [7:0] sample_length;      // Length of sample
	logic [11:0] bytes_remaining;      // 12 bits bytes left counter 0 - 4081.
	logic [7:0] sample_buffer;    // Next value to be loaded into shift reg

	logic [8:0] dmc_lsfr;
	logic [7:0] dmc_volume, dmc_volume_next;
	logic dmc_silence;
	logic have_buffer;
	logic [7:0] sample_shift;
	logic [2:0] dmc_bits; // Simply an 8 cycle counter.
	logic enable_1, enable_2, enable_3;
	logic do_adjust;

	logic [8:0] pal_pitch_lut[16];
	assign pal_pitch_lut = '{
		9'h1D7, 9'h067, 9'h0D9, 9'h143,
		9'h1E1, 9'h07B, 9'h05C, 9'h132,
		9'h04A, 9'h1A3, 9'h1CF, 9'h1CD,
		9'h02A, 9'h11C, 9'h11B, 9'h157
	};

	logic [8:0] ntsc_pitch_lut[16];
	assign ntsc_pitch_lut = '{
		9'h19D, 9'h0A2, 9'h185, 9'h1B6,
		9'h0EF, 9'h1F8, 9'h17C, 9'h117,
		9'h120, 9'h076, 9'h11E, 9'h13E,
		9'h162, 9'h123, 9'h0E3, 9'h0D5
	};

	assign Sample = dmc_volume[6:0];
	assign dma_req = ~have_buffer & enable & enable_3;
	logic dmc_clock;

	logic reload_next;
	always_ff @(posedge clk) begin
		if (write_ce) begin
			case (ain)
			0: begin  // $4010 // Applies at aclk1.
					irq_enable <= DIN[7];
					loop <= DIN[6];
					frequency <= DIN[3:0];
					if (~DIN[7]) irq <= 0;
				end
			1: begin  // $4011 Applies immediately, can be overwritten before aclk1
					dmc_volume <= {MMC5 & DIN[7], DIN[6:0]};
				end
			2: begin  // $4012 applies immediately
					sample_address <= MMC5 ? 15'h00 : {1'b1, DIN[7:0], 6'b000000};
				end
			3: begin  // $4013 applies immediately
					sample_length <= MMC5 ? 8'h0 : DIN[7:0];
				end
			5: begin // $4015
					irq <= 0; // Applies immediately
					enable <= DIN[4]; // Applies instantly -- there is a delayed version for DMC alignment
					// If the DMC bit is set, the DMC sample will be restarted only if not already active.
					if (~DIN[4])
						bytes_remaining <= 0;

					if (DIN[4] && ~|bytes_remaining) begin
						dma_address <= {1'b1, sample_address};
						bytes_remaining <= {sample_length, 4'b0000};
					end
				end
			endcase
		end

		if (aclk1_d) begin
			enable_1 <= enable;
			enable_2 <= enable_1;
			dmc_lsfr <= {dmc_lsfr[7:0], (dmc_lsfr[8] ^ dmc_lsfr[4]) | ~|dmc_lsfr};

			if (dmc_clock) begin
				dmc_clock <= 0;
				dmc_lsfr <= PAL ? pal_pitch_lut[frequency] : ntsc_pitch_lut[frequency];
				sample_shift <= {1'b0, sample_shift[7:1]};
				dmc_bits <= dmc_bits + 1'd1;

				if (&dmc_bits) begin // FIXME: Verify that 7->0 is the reload not 0->1.
					dmc_silence <= ~have_buffer;
					sample_shift <= sample_buffer;
					have_buffer <= 0;
					if (~dmc_silence) begin
						if (~sample_shift[0]) begin
							if (dmc_volume_next >= 2) begin
								dmc_volume <= dmc_volume_next - 2'd2;
							end
						end else begin
							if(dmc_volume_next <= 125) begin
								dmc_volume <= dmc_volume_next + 2'd2;
							end
						end
					end
				end
			end

			if (dma_ack) begin
				dma_address[14:0] <= dma_address[14:0] + 1'd1;
				bytes_remaining <= bytes_remaining - 1'd1;
				have_buffer <= 1;
				sample_buffer <= dma_data;
				if (bytes_remaining == 0) begin
					dma_address <= {1'b1, sample_address};
					bytes_remaining <= {sample_length, 4'b0000};
					enable <= loop;
					if (~loop & irq_enable) // FIXME: Should be at previous phi2?
						irq <= 1;
				end
			end
		end

		// Volume adjustment is done on aclk1. Technically, the value written to 4011 is immediately
		// applied, but won't "stick" if it conflicts with a lsfr clocked do-adjust.
		if (aclk1) begin
			enable_1 <= enable;
			enable_3 <= enable_2;

			dmc_volume_next <= dmc_volume;

			if (dmc_lsfr == 9'h100) begin
				dmc_clock <= 1;
			end
		end

		if (reset) begin
			irq_enable <= 0;
			irq <= 0;
			loop <= 0;
			frequency <= 0;
			dmc_volume <= 0;
			sample_shift <= 8'h0;
			dmc_lsfr <= cold_reset ? 9'd0 : (PAL ? pal_pitch_lut[0] : ntsc_pitch_lut[0]);
			bytes_remaining <= 0;
			dmc_bits <= 0;
			sample_buffer <= 0;
			have_buffer <= 0;
			enable <= 0;
			enable_1 <= 0;
			enable_2 <= 0;
			do_adjust <= 0;
		end

		if (cold_reset) begin
			sample_address <= 15'h0000;
			sample_length <= 1;
			dma_address <= 16'h8000;
		end

	end


endmodule

module FrameCtr (
	input  logic clk,
	input  logic aclk1,
	input  logic aclk2,
	input  logic reset,
	input  logic cold_reset,
	input  logic write,
	input  logic read,
	input  logic write_ce,
	input  logic [7:0] din,
	input  logic [1:0] addr,
	input  logic PAL,
	input  logic MMC5,
	output logic irq,
	output logic irq_flag,
	output logic frame_half,
	output logic frame_quarter
);

	// NTSC -- Confirmed
	// Binary Frame Value         Decimal  Cycle
	// 15'b001_0000_0110_0001,    04193    03713 -- Quarter
	// 15'b011_0110_0000_0011,    13827    07441 -- Half
	// 15'b010_1100_1101_0011,    11475    11170 -- 3 quarter
	// 15'b000_1010_0001_1111,    02591    14899 -- Reset w/o Seq/Interrupt
	// 15'b111_0001_1000_0101     29061    18625 -- Reset w/ seq

	// PAL -- Speculative
	// Binary Frame Value         Decimal  Cycle
	// 15'b001_1111_1010_0100     08100    04156
	// 15'b100_0100_0011_0000     17456    08313
	// 15'b101_1000_0001_0101     22549    12469
	// 15'b000_1011_1110_1000     03048    16625
	// 15'b000_0100_1111_1010     01274    20782

	logic frame_reset;
	logic frame_interrupt_buffer;
	logic frame_int_disabled;
	logic FrameInterrupt;
	logic frame_irq, set_irq;
	logic FrameSeqMode_2;
	logic frame_reset_2;
	logic w4017_1, w4017_2;

	// Proper state

	// Frame counter LFSR
	logic [14:0] frame;

	// Register 4017
	logic DisableFrameInterrupt;
	logic FrameSeqMode;

	assign frame_int_disabled = DisableFrameInterrupt | (write && addr == 5'h17 && din[6]);
	assign irq = FrameInterrupt && ~DisableFrameInterrupt;
	assign irq_flag = frame_interrupt_buffer;

	// This is implemented from the original LSFR frame counter logic taken from the 2A03 netlists. The
	// PAL LFSR numbers are educated guesses based on existing observed cycle numbers, but they may not
	// be perfectly correct.

	logic seq_mode;
	assign seq_mode = aclk1 ? FrameSeqMode : FrameSeqMode_2;

	logic frm_a, frm_b, frm_c, frm_d, frm_e;
	assign frm_a = (PAL ? 15'b001_1111_1010_0100 : 15'b001_0000_0110_0001) == frame;
	assign frm_b = (PAL ? 15'b100_0100_0011_0000 : 15'b011_0110_0000_0011) == frame;
	assign frm_c = (PAL ? 15'b101_1000_0001_0101 : 15'b010_1100_1101_0011) == frame;
	assign frm_d = (PAL ? 15'b000_1011_1110_1000 : 15'b000_1010_0001_1111) == frame && ~seq_mode;
	assign frm_e = (PAL ? 15'b000_0100_1111_1010 : 15'b111_0001_1000_0101) == frame;

	assign set_irq = frm_d & ~FrameSeqMode;
	assign frame_reset = frm_d | frm_e | w4017_2;
	assign frame_half = (frm_b | frm_d | frm_e | (w4017_2 & seq_mode));
	assign frame_quarter = (frm_a | frm_b | frm_c | frm_d | frm_e | (w4017_2 & seq_mode));

	always_ff @(posedge clk) begin : apu_block

		if (aclk1) begin
			frame <= frame_reset_2 ? 15'h7FFF : {frame[13:0], ((frame[14] ^ frame[13]) | ~|frame)};
			w4017_2 <= w4017_1;
			w4017_1 <= 0;
			FrameSeqMode_2 <= FrameSeqMode;
			frame_reset_2 <= 0;
		end

		if (aclk2 & frame_reset)
			frame_reset_2 <= 1;

		// Continously update the Frame IRQ state and read buffer
		if (set_irq & ~frame_int_disabled) begin
			FrameInterrupt <= 1;
			frame_interrupt_buffer <= 1;
		end else if (addr == 2'h1 && read)
			FrameInterrupt <= 0;
		else
			frame_interrupt_buffer <= FrameInterrupt;

		if (frame_int_disabled)
			FrameInterrupt <= 0;

		if (write_ce && addr == 3 && ~MMC5) begin  // Register $4017
			FrameSeqMode <= din[7];
			DisableFrameInterrupt <= din[6];
			w4017_1 <= 1;
		end

		if (reset) begin
			FrameInterrupt <= 0;
			frame_interrupt_buffer <= 0;
			w4017_1 <= 0;
			w4017_2 <= 0;
			DisableFrameInterrupt <= 0;
			if (cold_reset) FrameSeqMode <= 0; // Don't reset this on warm reset
			frame <= 15'h7FFF;
		end
	end

endmodule

module APU (
	input  logic        MMC5,
	input  logic        clk,
	input  logic        PHI2,
	input  logic        ce,
	input  logic        reset,
	input  logic        cold_reset,
	input  logic        PAL,
	input  logic  [4:0] ADDR,           // APU Address Line
	input  logic  [7:0] DIN,            // Data to APU
	input  logic        RW,
	input  logic        CS,
	input  logic  [4:0] audio_channels, // Enabled audio channels
	input  logic  [7:0] DmaData,        // Input data to DMC from memory.
	input  logic        odd_or_even,
	input  logic        DmaAck,         // 1 when DMC byte is on DmcData. DmcDmaRequested should go low.
	output logic  [7:0] DOUT,           // Data from APU
	output logic [15:0] Sample,
	output logic        DmaReq,         // 1 when DMC wants DMA
	output logic [15:0] DmaAddr,        // Address DMC wants to read
	output logic        IRQ             // IRQ asserted high == asserted
);

	// APU reads and writes happen at Phi2 of the 6502 core. Note: Not M2.
	logic read, read_old;
	logic write, write_ce, write_old;
	logic phi2_old, phi2_ce;

	assign read = RW & CS;
	assign write = ~RW & CS;
	assign phi2_ce = PHI2 & ~phi2_old;
	assign write_ce = write & phi2_ce;

	// The APU has four primary clocking events that take place:
	// aclk1    -- Aligned with CPU phi1, but every other cpu tick. This drives the majority of the APU
	// aclk1_d  -- Aclk1, except delayed by 1 cpu cycle exactly. Drives he half/quarter signals and len counter
	// aclk2    -- Aligned with CPU phi2, also every other frame
	// write    -- Happens on CPU phi2 (Not M2!). Most of these are latched by one of the above clocks.
	logic aclk1, aclk2, aclk1_delayed, phi1;
	assign aclk1 = ce & odd_or_even;          // Defined as the cpu tick when the frame counter increases
	assign aclk2 = phi2_ce;                   // Tick on odd cycles, not 50% duty cycle so it covers 2 cpu cycles
	assign aclk1_delayed = ce & ~odd_or_even; // Ticks 1 cpu cycle after frame counter
	assign phi1 = ce;

	logic [4:0] Enabled;
	logic [3:0] Sq1Sample,Sq2Sample,TriSample,NoiSample;
	logic [6:0] DmcSample;
	logic DmcIrq;
	logic IsDmcActive;

	logic irq_flag;
	logic frame_irq;

	// Generate internal memory write signals
	logic ApuMW0, ApuMW1, ApuMW2, ApuMW3, ApuMW4, ApuMW5;
	assign ApuMW0 = ADDR[4:2]==0; // SQ1
	assign ApuMW1 = ADDR[4:2]==1; // SQ2
	assign ApuMW2 = ADDR[4:2]==2; // TRI
	assign ApuMW3 = ADDR[4:2]==3; // NOI
	assign ApuMW4 = ADDR[4:2]>=4; // DMC
	assign ApuMW5 = ADDR[4:2]==5; // Control registers

	logic Sq1NonZero, Sq2NonZero, TriNonZero, NoiNonZero;
	logic ClkE, ClkL;

	logic [4:0] enabled_buffer, enabled_buffer_1;
	assign Enabled = aclk1 ? enabled_buffer : enabled_buffer_1;

	always_ff @(posedge clk) begin
		phi2_old <= PHI2;

		if (aclk1) begin
			enabled_buffer_1 <= enabled_buffer;
		end

		if (ApuMW5 && write_ce && ADDR[1:0] == 1) begin
			enabled_buffer <= DIN[4:0]; // Register $4015
		end

		if (reset) begin
			enabled_buffer <= 0;
			enabled_buffer_1 <= 0;
		end
	end

	logic frame_quarter, frame_half;
	assign ClkE = (frame_quarter & aclk1_delayed);
	assign ClkL = (frame_half & aclk1_delayed);

	// Generate bus output
	assign DOUT = {DmcIrq, irq_flag, 1'b0, IsDmcActive, NoiNonZero, TriNonZero,
		Sq2NonZero, Sq1NonZero};

	assign IRQ = frame_irq || DmcIrq;

	// Generate each channel
	SquareChan Squ1 (
		.MMC5         (MMC5),
		.clk          (clk),
		.ce           (ce),
		.aclk1        (aclk1),
		.reset        (reset),
		.cold_reset   (cold_reset),
		.sq2          (1'b0),
		.Addr         (ADDR[1:0]),
		.DIN          (DIN),
		.write        (ApuMW0 && write_ce),
		.LenCtr_Clock (ClkL),
		.Env_Clock    (ClkE),
		.odd_or_even  (odd_or_even),
		.Enabled      (Enabled[0]),
		.Sample       (Sq1Sample),
		.IsNonZero    (Sq1NonZero)
	);

	SquareChan Squ2 (
		.MMC5         (MMC5),
		.clk          (clk),
		.ce           (ce),
		.aclk1        (aclk1),
		.reset        (reset),
		.cold_reset   (cold_reset),
		.sq2          (1'b1),
		.Addr         (ADDR[1:0]),
		.DIN          (DIN),
		.write        (ApuMW1 && write_ce),
		.LenCtr_Clock (ClkL),
		.Env_Clock    (ClkE),
		.odd_or_even  (odd_or_even),
		.Enabled      (Enabled[1]),
		.Sample       (Sq2Sample),
		.IsNonZero    (Sq2NonZero)
	);

	TriangleChan Tri (
		.clk          (clk),
		.phi1         (phi1),
		.aclk1        (aclk1),
		.reset        (reset),
		.cold_reset   (cold_reset),
		.Addr         (ADDR[1:0]),
		.DIN          (DIN),
		.MW           (ApuMW2 && write_ce),
		.LenCtr_Clock (ClkL),
		.LinCtr_Clock (ClkE),
		.Enabled      (Enabled[2]),
		.Sample       (TriSample),
		.IsNonZero    (TriNonZero)
	);

	NoiseChan Noi (
		.clk          (clk),
		.ce           (ce),
		.aclk1        (aclk1),
		.aclk1_d      (aclk1_delayed),
		.reset        (reset),
		.cold_reset   (cold_reset),
		.Addr         (ADDR[1:0]),
		.DIN          (DIN),
		.PAL          (PAL),
		.MW           (ApuMW3 && write_ce),
		.LenCtr_Clock (ClkL),
		.Env_Clock    (ClkE),
		.Enabled      (Enabled[3]),
		.Sample       (NoiSample),
		.IsNonZero    (NoiNonZero)
	);

	// DmcChan Dmc (
	// 	.MMC5         (MMC5),
	// 	.clk          (clk),
	// 	.ce           (ce),
	// 	.aclk1        (aclk1),
	// 	.reset        (reset),
	// 	.cold_reset   (cold_reset),
	// 	.odd_or_even  (odd_or_even),
	// 	.Addr         (ADDR[2:0]),
	// 	.DIN          (DIN),
	// 	.MW           (ApuMW4 && write_ce),
	// 	.Sample       (DmcSample),
	// 	.DmaReq       (DmaReq),
	// 	.DmaAck       (DmaAck),
	// 	.DmaAddr      (DmaAddr),
	// 	.DmaData      (DmaData),
	// 	.Irq          (DmcIrq),
	// 	.PAL          (PAL),
	// 	.IsDmcActive  (IsDmcActive)
	// );

	DmcChan2 Dmc (
		.MMC5        (MMC5),
		.clk         (clk),
		.phi1        (phi1),
		.aclk1       (aclk1),
		.aclk1_d     (aclk1_delayed),
		.reset       (reset),
		.cold_reset  (cold_reset),
		.ain         (ADDR[2:0]),
		.DIN         (DIN),
		.write_ce    (write_ce & ApuMW4),
		.write       (write & ApuMW4),
		.dma_ack     (DmaAck),
		.dma_data    (DmaData),
		.PAL         (PAL),
		.dma_address (DmaAddr),
		.irq         (DmcIrq),
		.Sample      (DmcSample),
		.dma_req     (DmaReq),
		.enable      (IsDmcActive)
	);

	APUMixer mixer (
		.square1      (Sq1Sample),
		.square2      (Sq2Sample),
		.noise        (NoiSample),
		.triangle     (TriSample),
		.dmc          (DmcSample),
		.sample       (Sample)
	);

	FrameCtr frame_counter (
		.clk          (clk),
		.aclk1        (aclk1),
		.aclk2        (aclk2),
		.reset        (reset),
		.cold_reset   (cold_reset),
		.write        (ApuMW5 & write),
		.read         (ApuMW5 & read),
		.write_ce     (ApuMW5 & write_ce),
		.addr         (ADDR[1:0]),
		.din          (DIN),
		.PAL          (PAL),
		.MMC5         (MMC5),
		.irq          (frame_irq),
		.irq_flag     (irq_flag),
		.frame_half   (frame_half),
		.frame_quarter(frame_quarter)
	);

endmodule

// http://wiki.nesdev.com/w/index.php/APU_Mixer
// I generated three LUT's for each mix channel entry and one lut for the squares, then a
// 282 entry lut for the mix channel. It's more accurate than the original LUT system listed on
// the NesDev page.

module APUMixer (
	input  logic  [3:0] square1,
	input  logic  [3:0] square2,
	input  logic  [3:0] triangle,
	input  logic  [3:0] noise,
	input  logic  [6:0] dmc,
	output logic [15:0] sample
);

logic [15:0] pulse_lut[32];
assign pulse_lut = '{
	16'd0,     16'd763,   16'd1509,  16'd2236,  16'd2947,  16'd3641,  16'd4319,  16'd4982,
	16'd5630,  16'd6264,  16'd6883,  16'd7490,  16'd8083,  16'd8664,  16'd9232,  16'd9789,
	16'd10334, 16'd10868, 16'd11392, 16'd11905, 16'd12408, 16'd12901, 16'd13384, 16'd13858,
	16'd14324, 16'd14780, 16'd15228, 16'd15668, 16'd16099, 16'd16523, 16'd16939, 16'd17348
};

logic [5:0] tri_lut[16];
assign tri_lut = '{
	6'd0,  6'd3,  6'd7,  6'd11, 6'd15, 6'd19, 6'd23, 6'd27,
	6'd31, 6'd35, 6'd39, 6'd43, 6'd47, 6'd51, 6'd55, 6'd59
};

logic [5:0] noise_lut[16];
assign noise_lut = '{
	6'd0,  6'd2,  6'd5,  6'd8,  6'd10, 6'd13, 6'd16, 6'd18,
	6'd21, 6'd24, 6'd26, 6'd29, 6'd32, 6'd34, 6'd37, 6'd40
};

logic [7:0] dmc_lut[128];
assign dmc_lut = '{
	8'd0,   8'd1,   8'd2,   8'd4,   8'd5,   8'd7,   8'd8,   8'd10,  8'd11,  8'd13,  8'd14,  8'd15,  8'd17,  8'd18,  8'd20,  8'd21,
	8'd23,  8'd24,  8'd26,  8'd27,  8'd28,  8'd30,  8'd31,  8'd33,  8'd34,  8'd36,  8'd37,  8'd39,  8'd40,  8'd41,  8'd43,  8'd44,
	8'd46,  8'd47,  8'd49,  8'd50,  8'd52,  8'd53,  8'd55,  8'd56,  8'd57,  8'd59,  8'd60,  8'd62,  8'd63,  8'd65,  8'd66,  8'd68,
	8'd69,  8'd70,  8'd72,  8'd73,  8'd75,  8'd76,  8'd78,  8'd79,  8'd81,  8'd82,  8'd83,  8'd85,  8'd86,  8'd88,  8'd89,  8'd91,
	8'd92,  8'd94,  8'd95,  8'd96,  8'd98,  8'd99,  8'd101, 8'd102, 8'd104, 8'd105, 8'd107, 8'd108, 8'd110, 8'd111, 8'd112, 8'd114,
	8'd115, 8'd117, 8'd118, 8'd120, 8'd121, 8'd123, 8'd124, 8'd125, 8'd127, 8'd128, 8'd130, 8'd131, 8'd133, 8'd134, 8'd136, 8'd137,
	8'd138, 8'd140, 8'd141, 8'd143, 8'd144, 8'd146, 8'd147, 8'd149, 8'd150, 8'd151, 8'd153, 8'd154, 8'd156, 8'd157, 8'd159, 8'd160,
	8'd162, 8'd163, 8'd165, 8'd166, 8'd167, 8'd169, 8'd170, 8'd172, 8'd173, 8'd175, 8'd176, 8'd178, 8'd179, 8'd180, 8'd182, 8'd183
};

logic [15:0] mix_lut[512];
assign mix_lut = '{
	16'd0,     16'd318,   16'd635,   16'd950,   16'd1262,  16'd1573,  16'd1882,  16'd2190,  16'd2495,  16'd2799,  16'd3101,  16'd3401,  16'd3699,  16'd3995,  16'd4290,  16'd4583,
	16'd4875,  16'd5164,  16'd5452,  16'd5739,  16'd6023,  16'd6306,  16'd6588,  16'd6868,  16'd7146,  16'd7423,  16'd7698,  16'd7971,  16'd8243,  16'd8514,  16'd8783,  16'd9050,
	16'd9316,  16'd9581,  16'd9844,  16'd10105, 16'd10365, 16'd10624, 16'd10881, 16'd11137, 16'd11392, 16'd11645, 16'd11897, 16'd12147, 16'd12396, 16'd12644, 16'd12890, 16'd13135,
	16'd13379, 16'd13622, 16'd13863, 16'd14103, 16'd14341, 16'd14579, 16'd14815, 16'd15050, 16'd15284, 16'd15516, 16'd15747, 16'd15978, 16'd16206, 16'd16434, 16'd16661, 16'd16886,
	16'd17110, 16'd17333, 16'd17555, 16'd17776, 16'd17996, 16'd18215, 16'd18432, 16'd18649, 16'd18864, 16'd19078, 16'd19291, 16'd19504, 16'd19715, 16'd19925, 16'd20134, 16'd20342,
	16'd20549, 16'd20755, 16'd20960, 16'd21163, 16'd21366, 16'd21568, 16'd21769, 16'd21969, 16'd22169, 16'd22367, 16'd22564, 16'd22760, 16'd22955, 16'd23150, 16'd23343, 16'd23536,
	16'd23727, 16'd23918, 16'd24108, 16'd24297, 16'd24485, 16'd24672, 16'd24858, 16'd25044, 16'd25228, 16'd25412, 16'd25595, 16'd25777, 16'd25958, 16'd26138, 16'd26318, 16'd26497,
	16'd26674, 16'd26852, 16'd27028, 16'd27203, 16'd27378, 16'd27552, 16'd27725, 16'd27898, 16'd28069, 16'd28240, 16'd28410, 16'd28579, 16'd28748, 16'd28916, 16'd29083, 16'd29249,
	16'd29415, 16'd29580, 16'd29744, 16'd29907, 16'd30070, 16'd30232, 16'd30393, 16'd30554, 16'd30714, 16'd30873, 16'd31032, 16'd31190, 16'd31347, 16'd31503, 16'd31659, 16'd31815,
	16'd31969, 16'd32123, 16'd32276, 16'd32429, 16'd32581, 16'd32732, 16'd32883, 16'd33033, 16'd33182, 16'd33331, 16'd33479, 16'd33627, 16'd33774, 16'd33920, 16'd34066, 16'd34211,
	16'd34356, 16'd34500, 16'd34643, 16'd34786, 16'd34928, 16'd35070, 16'd35211, 16'd35352, 16'd35492, 16'd35631, 16'd35770, 16'd35908, 16'd36046, 16'd36183, 16'd36319, 16'd36456,
	16'd36591, 16'd36726, 16'd36860, 16'd36994, 16'd37128, 16'd37261, 16'd37393, 16'd37525, 16'd37656, 16'd37787, 16'd37917, 16'd38047, 16'd38176, 16'd38305, 16'd38433, 16'd38561,
	16'd38689, 16'd38815, 16'd38942, 16'd39068, 16'd39193, 16'd39318, 16'd39442, 16'd39566, 16'd39690, 16'd39813, 16'd39935, 16'd40057, 16'd40179, 16'd40300, 16'd40421, 16'd40541,
	16'd40661, 16'd40780, 16'd40899, 16'd41017, 16'd41136, 16'd41253, 16'd41370, 16'd41487, 16'd41603, 16'd41719, 16'd41835, 16'd41950, 16'd42064, 16'd42178, 16'd42292, 16'd42406,
	16'd42519, 16'd42631, 16'd42743, 16'd42855, 16'd42966, 16'd43077, 16'd43188, 16'd43298, 16'd43408, 16'd43517, 16'd43626, 16'd43735, 16'd43843, 16'd43951, 16'd44058, 16'd44165,
	16'd44272, 16'd44378, 16'd44484, 16'd44589, 16'd44695, 16'd44799, 16'd44904, 16'd45008, 16'd45112, 16'd45215, 16'd45318, 16'd45421, 16'd45523, 16'd45625, 16'd45726, 16'd45828,
	16'd45929, 16'd46029, 16'd46129, 16'd46229, 16'd46329, 16'd46428, 16'd46527, 16'd46625, 16'd46723, 16'd46821, 16'd46919, 16'd47016, 16'd47113, 16'd47209, 16'd47306, 16'd47402,
	16'd47497, 16'd47592, 16'd47687, 16'd47782, 16'd47876, 16'd47970, 16'd48064, 16'd48157, 16'd48250, 16'd48343, 16'd48436, 16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,
	16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0,     16'd0
};

wire [4:0] squares = square1 + square2;
wire [8:0] mix = tri_lut[triangle] + noise_lut[noise] + dmc_lut[dmc];
wire [15:0] ch1 = pulse_lut[squares];
wire [15:0] ch2 = mix_lut[mix];
wire [63:0] chan_mix = ch1 + ch2;

assign sample = chan_mix > 16'hFFFF ? 16'hFFFF : chan_mix[15:0];

endmodule
