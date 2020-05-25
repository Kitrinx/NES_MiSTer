// Copyright (c) 2012-2013 Ludvig Strigeus
// This program is GPL Licensed. See COPYING for the full license.

module SquareChan (
	input  logic       MMC5,
	input  logic       clk,
	input  logic       ce,
	input  logic       reset,
	input  logic       sq2,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       MW,
	input  logic       LenCtr_Clock,
	input  logic       Env_Clock,
	input  logic       odd_or_even,
	input  logic       Enabled,
	input  logic [7:0] LenCtr_In,
	output logic [3:0] Sample,
	output logic       IsNonZero
);

reg [7:0] LenCtr;

// Register 1
reg [1:0] Duty;
reg EnvLoop, EnvDisable, EnvDoReset;
reg [3:0] Volume, Envelope, EnvDivider;
wire LenCtrHalt = EnvLoop; // Aliased bit
assign IsNonZero = (LenCtr != 0);
// Register 2
reg SweepEnable, SweepNegate, SweepReset;
reg [2:0] SweepPeriod, SweepDivider, SweepShift;

reg [10:0] Period;
reg [11:0] TimerCtr;
reg [2:0] SeqPos;
wire [10:0] ShiftedPeriod = (Period >> SweepShift);
wire [10:0] PeriodRhs = (SweepNegate ? (~ShiftedPeriod + {10'b0, sq2}) : ShiftedPeriod);
wire [11:0] NewSweepPeriod = Period + PeriodRhs;
// XXX: This should be enabled for MMC5, but do we really want ultrasonic frequencies?
// Re-enable if we ever get a proper LPF.
wire ValidFreq = /*(MMC5==1) ||*/ ((|Period[10:3]) && (SweepNegate || !NewSweepPeriod[11]));
 // |Period[10:3] is equivalent to Period >= 8

//double speed for MMC5=Env_Clock
wire LenCtrClockEnable = (MMC5==0 && LenCtr_Clock) || (MMC5==1 && Env_Clock);

always @(posedge clk) begin
	if (reset) begin
		LenCtr <= 0;
		Duty <= 0;
		EnvDoReset <= 0;
		EnvLoop <= 0;
		EnvDisable <= 0;
		Volume <= 0;
		Envelope <= 0;
		EnvDivider <= 0;
		SweepEnable <= 0;
		SweepNegate <= 0;
		SweepReset <= 0;
		SweepPeriod <= 0;
		SweepDivider <= 0;
		SweepShift <= 0;
		Period <= 0;
		TimerCtr <= 0;
		SeqPos <= 0;
	end else if (ce) begin
	// Count down the square timer...
	// Should be clocked on every even cpu cycle
	if (~odd_or_even) begin
		if (TimerCtr == 0) begin
			// Timer was clocked
			TimerCtr <= Period;
			SeqPos <= SeqPos - 1'd1;
		end else begin
			TimerCtr <= TimerCtr - 1'd1;
		end
	end

	// Clock the length counter?
	if (LenCtrClockEnable && LenCtr != 0 && !LenCtrHalt) begin
		LenCtr <= LenCtr - 1'd1;
	end

	// Clock the sweep unit?
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

	// Clock the envelope generator?
	if (Env_Clock) begin
		if (EnvDoReset) begin
			EnvDivider <= Volume;
			Envelope <= 15;
			EnvDoReset <= 0;
		end else if (EnvDivider == 0) begin
			EnvDivider <= Volume;
			if (Envelope != 0 || EnvLoop)
				Envelope <= Envelope - 1'd1;
		end else begin
			EnvDivider <= EnvDivider - 1'd1;
		end
	end

	// Length counter forced to zero if disabled.

	end else if (MW) begin
		case(Addr)
		0: begin
			Duty <= DIN[7:6];
			EnvLoop <= DIN[5];
			EnvDisable <= DIN[4];
			Volume <= DIN[3:0];
		end
		1: begin
		if (MMC5==0) begin
			SweepEnable <= DIN[7];
			SweepPeriod <= DIN[6:4];
			SweepNegate <= DIN[3];
			SweepShift <= DIN[2:0];
			SweepReset <= 1;
		end
		end
		2: begin
			Period[7:0] <= DIN;
		end
		3: begin
			// Upper bits of the period
			Period[10:8] <= DIN[2:0];
			LenCtr <= LenCtr_In;
			EnvDoReset <= 1;
			SeqPos <= 0;
		end
		endcase
	end

if (!Enabled)
		LenCtr <= 0;
end

wire DutyEnabledUsed = (MMC5==1) ^ DutyEnabled;

reg DutyEnabled;
always @* begin
	// Determine if the duty is enabled or not
	case (Duty)
	0: DutyEnabled = (SeqPos == 7);
	1: DutyEnabled = (SeqPos >= 6);
	2: DutyEnabled = (SeqPos >= 4);
	3: DutyEnabled = (SeqPos < 6);
	endcase

	// Compute the output
	if (LenCtr == 0 || !ValidFreq || !DutyEnabledUsed)
		Sample = 0;
	else
		Sample = EnvDisable ? Volume : Envelope;
end
endmodule

module TriangleChan (
	input  logic       clk,
	input  logic       ce,
	input  logic       reset,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       MW,
	input  logic       LenCtr_Clock,
	input  logic       LinCtr_Clock,
	input  logic       Enabled,
	input  logic [7:0] LenCtr_In,
	output logic [3:0] Sample,
	output logic       IsNonZero
);
	//
	reg [10:0] Period, TimerCtr;
	reg [4:0] SeqPos;
	//
	// Linear counter state
	reg [6:0] LinCtrPeriod, LinCtr;
	reg LinCtrl, LinHalt;
	wire LinCtrZero = (LinCtr == 0);
	//
	// Length counter state
	reg [7:0] LenCtr;
	wire LenCtrHalt = LinCtrl; // Aliased bit
	wire LenCtrZero = (LenCtr == 0);
	assign IsNonZero = !LenCtrZero;
	//
	always @(posedge clk) begin
	if (reset) begin
		Period <= 0;
		TimerCtr <= 0;
		SeqPos <= 0;
		LinCtrPeriod <= 0;
		LinCtr <= 0;
		//LinCtrl <= 0; do not reset
		LinHalt <= 0;
		LenCtr <= 0;
	end else if (ce) begin
		// Check if writing to the regs of this channel


		// Count down the period timer...
		if (TimerCtr == 0) begin
			TimerCtr <= Period;
		end else begin
			TimerCtr <= TimerCtr - 1'd1;
		end
		//
		// Clock the length counter?
		if (LenCtr_Clock && !LenCtrZero && !LenCtrHalt) begin
			LenCtr <= LenCtr - 1'd1;
		end
		//
		// Clock the linear counter?
		if (LinCtr_Clock) begin
			if (LinHalt)
				LinCtr <= LinCtrPeriod;
			else if (!LinCtrZero)
				LinCtr <= LinCtr - 1'd1;
			if (!LinCtrl)
				LinHalt <= 0;
		end
		//
		// Length counter forced to zero if disabled.

			//
		// Clock the sequencer position
		if (TimerCtr == 0 && !LenCtrZero && !LinCtrZero)
			SeqPos <= SeqPos + 1'd1;
	end else if (MW) begin
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
			LenCtr <= LenCtr_In;
			LinHalt <= 1;
		end
		endcase
	end
	if (!Enabled)
			LenCtr <= 0;
	end
	// Generate the output
	// XXX: Ultrisonic frequencies cause issues, so are disabled.
	// This can be removed for accuracy if a proper LPF is ever implemented.
	always @(posedge clk)
		Sample <= (Period > 1) ? SeqPos[3:0] ^ {4{~SeqPos[4]}} : Sample;
	//
endmodule

module NoiseChan (
	input  logic       clk,
	input  logic       ce,
	input  logic       reset,
	input  logic [1:0] Addr,
	input  logic [7:0] DIN,
	input  logic       MW,
	input  logic       LenCtr_Clock,
	input  logic       Env_Clock,
	input  logic       Enabled,
	input  logic [7:0] LenCtr_In,
	output logic [3:0] Sample,
	output logic       IsNonZero
);
	//
	// Envelope volume
	reg EnvLoop, EnvDisable, EnvDoReset;
	reg [3:0] Volume, Envelope, EnvDivider;
	// Length counter
	wire LenCtrHalt = EnvLoop; // Aliased bit
	reg [7:0] LenCtr;
	//
	reg ShortMode;
	reg [14:0] Shift = 1;

	assign IsNonZero = (LenCtr != 0);
	//
	// Period stuff
	reg [3:0] Period;
	reg [11:0] NoisePeriod, TimerCtr;
	always @* begin
		case (Period)
		0: NoisePeriod = 12'd4;
		1: NoisePeriod = 12'd8;
		2: NoisePeriod = 12'd16;
		3: NoisePeriod = 12'd32;
		4: NoisePeriod = 12'd64;
		5: NoisePeriod = 12'd96;
		6: NoisePeriod = 12'd128;
		7: NoisePeriod = 12'd160;
		8: NoisePeriod = 12'd202;
		9: NoisePeriod = 12'd254;
		10: NoisePeriod = 12'd380;
		11: NoisePeriod = 12'd508;
		12: NoisePeriod = 12'd762;
		13: NoisePeriod = 12'd1016;
		14: NoisePeriod = 12'd2034;
		15: NoisePeriod = 12'd4068;
		endcase
	end
	//
	always @(posedge clk) begin
	if (reset) begin
		EnvLoop <= 0;
		EnvDisable <= 0;
		EnvDoReset <= 0;
		Volume <= 0;
		Envelope <= 0;
		EnvDivider <= 0;
		LenCtr <= 1;
		ShortMode <= 0;
		Shift <= 1;
		Period <= 0;
		TimerCtr <= NoisePeriod - 1'b1;
	end else if (ce) begin
		// Check if writing to the regs of this channel

		// Count down the period timer...
		if (TimerCtr == 0) begin
			TimerCtr <= NoisePeriod - 1'b1;
			// Clock the shift register. Use either
			// bit 1 or 6 as the tap.
			Shift <= {
				Shift[0] ^ (ShortMode ? Shift[6] : Shift[1]),
				Shift[14:1]};
		end else begin
			TimerCtr <= TimerCtr - 1'd1;
		end
		// Clock the length counter?
		if (LenCtr_Clock && LenCtr != 0 && !LenCtrHalt) begin
			LenCtr <= LenCtr - 1'd1;
		end
		// Clock the envelope generator?
		if (Env_Clock) begin
			if (EnvDoReset) begin
				EnvDivider <= Volume;
				Envelope <= 15;
				EnvDoReset <= 0;
			end else if (EnvDivider == 0) begin
				EnvDivider <= Volume;
				if (Envelope != 0)
					Envelope <= Envelope - 1'd1;
				else if (EnvLoop)
					Envelope <= 15;
			end else
				EnvDivider <= EnvDivider - 1'd1;
		end

	end else if (MW) begin
		case (Addr)
		0: begin
			EnvLoop <= DIN[5];
			EnvDisable <= DIN[4];
			Volume <= DIN[3:0];
		end
		2: begin
			ShortMode <= DIN[7];
			Period <= DIN[3:0];
		end
		3: begin
			LenCtr <= LenCtr_In;
			EnvDoReset <= 1;
		end
		endcase
	end
	if (!Enabled)
			LenCtr <= 0;
	end
	// Produce the output signal
	assign Sample =
		(LenCtr == 0 || Shift[0]) ?
			4'd0 :
			(EnvDisable ? Volume : Envelope);
endmodule

module DmcChan (
	input  logic        MMC5,
	input  logic        clk,
	input  logic        ce,
	input  logic        reset,
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
	reg IrqEnable;
	reg IrqActive;
	reg Loop;                 // Looping enabled
	reg [3:0] Freq;           // Current value of frequency register
	reg [7:0] Dac = 0;        // Current value of DAC
	reg [7:0] SampleAddress;  // Base address of sample
	reg [7:0] SampleLen;      // Length of sample
	reg [7:0] ShiftReg;       // Shift register
	reg [8:0] Cycles;         // Down counter, is the period
	reg [14:0] Address;        // 15 bits current address, 0x8000-0xffff
	reg [11:0] BytesLeft;      // 12 bits bytes left counter 0 - 4081.
	reg [2:0] BitsUsed;        // Number of bits left in the SampleBuffer.
	reg [7:0] SampleBuffer;    // Next value to be loaded into shift reg
	reg HasSampleBuffer;       // Sample buffer is nonempty
	reg HasShiftReg;           // Shift reg is non empty
	reg DmcEnabled;
	reg [1:0] ActivationDelay;
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

	// Shift register initially loaded with 07
	always @(posedge clk) begin
		if (reset) begin
			IrqEnable <= 0;
			IrqActive <= 0;
			Loop <= 0;
			Freq <= 0;
			Dac <= 0;
			SampleAddress <= 0;
			SampleLen <= 1;
			ShiftReg <= 8'h0; // XXX: should be 0 or 07? Visual 2C02 says 0, as does Mesen.
			Cycles <= 439;
			Address <= 15'h4000;
			BytesLeft <= 0;
			BitsUsed <= 0;
			SampleBuffer <= 0;
			HasSampleBuffer <= 0;
			HasShiftReg <= 0;
			DmcEnabled <= 0;
			ActivationDelay <= 0;
		end else if (ce) begin
			if (ActivationDelay == 3 && !odd_or_even) ActivationDelay <= 1;
			if (ActivationDelay == 1) ActivationDelay <= 0;

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
					Address <= {1'b1, SampleAddress, 6'b000000};
					BytesLeft <= {SampleLen, 4'b0000};
					DmcEnabled <= Loop;
					if (!Loop && IrqEnable)
						IrqActive <= 1;
				end
			end
		end else if (MW) begin
			case (Addr)
			0: begin  // $4010   il-- ffff   IRQ enable, loop, frequency index
					IrqEnable <= DIN[7];
					Loop <= DIN[6];
					Freq <= DIN[3:0];
					if (!DIN[7]) IrqActive <= 0;
				end
			1: begin  // $4011   -ddd dddd   DAC
					// This will get missed if the Dac <= far below runs, that is by design.
					Dac <= {(MMC5==1) && DIN[7],DIN[6:0]};
				end
			2: begin  // $4012   aaaa aaaa   sample address
					SampleAddress <= (MMC5==1) ? 8'h0 : DIN[7:0];
				end
			3: begin  // $4013   llll llll   sample length
					SampleLen <= (MMC5==1) ? 8'h0 : DIN[7:0];
				end
			5: begin // $4015 write	---D NT21  Enable DMC (D)
					IrqActive <= 0;
					DmcEnabled <= DIN[4];
					// If the DMC bit is set, the DMC sample will be restarted only if not already active.
					if (DIN[4] && !DmcEnabled) begin
						Address <= {1'b1, SampleAddress, 6'b000000};
						BytesLeft <= {SampleLen, 4'b0000};
						ActivationDelay <= 2'd3;
					end
				end
			endcase
		end
	end
endmodule

module APU (
	input  logic        MMC5,
	input  logic        clk,
	input  logic        PHI2,
	input  logic        ce,
	input  logic        reset,
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

logic [6:0] len_counter_lut[32];
logic read, read_old;
logic write, write_ce, write_old;
logic cs_old, cs_ce;
logic phi2_old, phi2_ce;

// APU reads and writes happen at Phi2 of the 6502 core. Note: Not M2.
assign read = RW & CS;
assign write = ~RW & CS;
assign phi2_ce = PHI2 & ~phi2_old;
assign write_ce = write & phi2_ce;

// Which channels are enabled?
reg [3:0] Enabled;

// Output samples from the 4 channels
wire [3:0] Sq1Sample,Sq2Sample,TriSample,NoiSample;

// Output samples from the DMC channel
wire [6:0] DmcSample;
wire DmcIrq;
wire IsDmcActive;

// Generate internal memory write signals
wire ApuMW0 = ADDR[4:2]==0; // SQ1
wire ApuMW1 = ADDR[4:2]==1; // SQ2
wire ApuMW2 = ADDR[4:2]==2; // TRI
wire ApuMW3 = ADDR[4:2]==3; // NOI
wire ApuMW4 = ADDR[4:2]>=4; // DMC
wire ApuMW5 = ADDR[4:2]==5; // Control registers

wire Sq1NonZero, Sq2NonZero, TriNonZero, NoiNonZero;

// Common input to all channels
logic [7:0] LenCtr_In;
assign LenCtr_In = {len_counter_lut[DIN[7:3]], 1'b0};

// Frame sequencer registers
reg FrameSeqMode;
logic ClkE, ClkL;

wire frame_irq = FrameInterrupt && !DisableFrameInterrupt;

// Generate bus output
assign DOUT = {DmcIrq, frame_interrupt_buffer, 1'b0, IsDmcActive, NoiNonZero, TriNonZero,
	Sq2NonZero, Sq1NonZero};

assign IRQ = frame_irq || DmcIrq;

// Generate each channel
SquareChan Squ1 (
	.MMC5         (MMC5),
	.clk          (clk),
	.ce           (ce),
	.reset        (reset),
	.sq2          (1'b0),
	.Addr         (ADDR[1:0]),
	.DIN          (DIN),
	.MW           (ApuMW0 && write_ce),
	.LenCtr_Clock (ClkL),
	.Env_Clock    (ClkE),
	.odd_or_even  (odd_or_even),
	.Enabled      (Enabled[0]),
	.LenCtr_In    (LenCtr_In),
	.Sample       (Sq1Sample),
	.IsNonZero    (Sq1NonZero)
);

SquareChan Squ2 (
	.MMC5         (MMC5),
	.clk          (clk),
	.ce           (ce),
	.reset        (reset),
	.sq2          (1'b1),
	.Addr         (ADDR[1:0]),
	.DIN          (DIN),
	.MW           (ApuMW1 && write_ce),
	.LenCtr_Clock (ClkL),
	.Env_Clock    (ClkE),
	.odd_or_even  (odd_or_even),
	.Enabled      (Enabled[1]),
	.LenCtr_In    (LenCtr_In),
	.Sample       (Sq2Sample),
	.IsNonZero    (Sq2NonZero)
);

TriangleChan Tri (
	.clk          (clk),
	.ce           (ce),
	.reset        (reset),
	.Addr         (ADDR[1:0]),
	.DIN          (DIN),
	.MW           (ApuMW2 && write_ce),
	.LenCtr_Clock (ClkL),
	.LinCtr_Clock (ClkE),
	.Enabled      (Enabled[2]),
	.LenCtr_In    (LenCtr_In),
	.Sample       (TriSample),
	.IsNonZero    (TriNonZero)
);

NoiseChan Noi (
	.clk          (clk),
	.ce           (ce),
	.reset        (reset),
	.Addr         (ADDR[1:0]),
	.DIN          (DIN),
	.MW           (ApuMW3 && write_ce),
	.LenCtr_Clock (ClkL),
	.Env_Clock    (ClkE),
	.Enabled      (Enabled[3]),
	.LenCtr_In    (LenCtr_In),
	.Sample       (NoiSample),
	.IsNonZero    (NoiNonZero)
);

DmcChan Dmc (
	.MMC5         (MMC5),
	.clk          (clk),
	.ce           (ce),
	.reset        (reset),
	.odd_or_even  (odd_or_even),
	.Addr         (ADDR[2:0]),
	.DIN          (DIN),
	.MW           (ApuMW4 && write_ce),
	.Sample       (DmcSample),
	.DmaReq       (DmaReq),
	.DmaAck       (DmaAck),
	.DmaAddr      (DmaAddr),
	.DmaData      (DmaData),
	.Irq          (DmcIrq),
	.PAL          (PAL),
	.IsDmcActive  (IsDmcActive)
);

APUMixer mixer (
	.square1      (Sq1Sample),
	.square2      (Sq2Sample),
	.noise        (NoiSample),
	.triangle     (TriSample),
	.dmc          (DmcSample),
	.sample       (Sample)
);

reg FrameInterrupt, DisableFrameInterrupt;

logic set_irq;
logic [14:0] frame;
logic aclk1;
logic aclk2;
logic aclk1_delayed;

logic w4017_1, w4017_2;

assign aclk1 = ce & odd_or_even;          // Defined as the cpu tick when the frame counter increases
assign aclk2 = phi2_ce;                   // Tick on odd cycles, not 50% duty cycle so it covers 2 cpu cycles
assign aclk1_delayed = ce & ~odd_or_even; // Ticks 1 cpu cycle after frame counter

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
logic frame_quarter;
logic frame_half;
logic frame_interrupt_buffer;

logic frame_int_disabled;
assign frame_int_disabled = DisableFrameInterrupt | (write && ADDR == 5'h17 && DIN[6]);

assign ClkE = (frame_quarter & aclk1_delayed);
assign ClkL = (frame_half & aclk1_delayed);

logic FrameSeqMode_2;
logic frame_reset_2;

// This is implemented from the original LSFR frame counter logic taken from the 2A03 netlists. The
// PAL LFSR numbers are educated guesses based on existing observed cycle numbers, but they may not
// be perfectly correct.

logic frm_a, frm_b, frm_c, frm_d, frm_e;
assign frm_a = (PAL ? 15'b001_1111_1010_0100 : 15'b001_0000_0110_0001) == frame;
assign frm_b = (PAL ? 15'b100_0100_0011_0000 : 15'b011_0110_0000_0011) == frame;
assign frm_c = (PAL ? 15'b101_1000_0001_0101 : 15'b010_1100_1101_0011) == frame;
assign frm_d = (PAL ? 15'b000_1011_1110_1000 : 15'b000_1010_0001_1111) == frame && ~FrameSeqMode_2;
assign frm_e = (PAL ? 15'b000_0100_1111_1010 : 15'b111_0001_1000_0101) == frame;

assign set_irq = frm_d & ~FrameSeqMode;
assign frame_reset = frm_d | frm_e | w4017_2;
assign frame_half = (frm_b | frm_d | frm_e | (w4017_2 & FrameSeqMode_2));
assign frame_quarter = (frm_a | frm_b | frm_c | frm_d | frm_e | (w4017_2 & FrameSeqMode_2));

always_ff @(posedge clk) begin
	phi2_old <= PHI2;

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
	end else if (ADDR == 5'h15 && read)
		FrameInterrupt <= 0;
	else
		frame_interrupt_buffer <= FrameInterrupt;

	if (frame_int_disabled)
		FrameInterrupt <= 0;

	// Writes take place on Phi2
	if (ApuMW5 && write_ce) begin
		case (ADDR[1:0])
			1: Enabled <= DIN[3:0]; // Register $4015
			3: begin                // Register $4017
				if (~MMC5) begin
					FrameSeqMode <= DIN[7];
					DisableFrameInterrupt <= DIN[6];
					w4017_1 <= 1;
				end
			end
		endcase
	end

	if (reset) begin
		FrameInterrupt <= 0;
		frame_interrupt_buffer <= 0;
		w4017_1 <= 0;
		w4017_2 <= 0;
		Enabled <= 0;
		//{FrameSeqMode, DisableFrameInterrupt} <= last_4017[1:0]; // Don't reset these
		frame <= 15'h7FFF; // initializes to all 1's
	end
end

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

endmodule

// http://wiki.nesdev.com/w/index.php/APU_Mixer
// I generated three LUT's for each mix channel entry and one lut for the squares, then a
// 282 entry lut for the mix channel. It's more accurate than the original LUT system listed on
// the NesDev page.

module APUMixer (
	input [3:0] square1,
	input [3:0] square2,
	input [3:0] triangle,
	input [3:0] noise,
	input [6:0] dmc,
	output [15:0] sample
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
