// Buggy 4-to-16 Decoder


module buggy_decoder (
    input  logic        clk,          // Clock for timing analysis
    input  logic        enable,       // Active high enable
    input  logic [3:0]  select,       // 4-bit input select
    output logic [15:0] out           // 16-bit decoded output
);

    logic [3:0] select_reg;  // BUG: Unnecessary register adding delay
    logic enable_reg;        // BUG: Unnecessary enable registration

    // BUG: Unnecessary sequential logic for combinatorial decoder
    always_ff @(posedge clk) begin
        select_reg <= select;
        enable_reg <= enable;
    end

    // BUG: Complex combinational logic with potential timing issues
    always_comb begin
        // Default assignment
        out = 16'h0000;

        // BUG: Wrong enable logic polarity
        if (!enable_reg) begin  // Should be enable_reg
            // BUG: Using registered select instead of direct input
            case (select_reg)
                4'b0000: out = 16'h0001;
                4'b0001: out = 16'h0002;
                4'b0010: out = 16'h0004;
                4'b0011: out = 16'h0008;
                4'b0100: out = 16'h0010;
                4'b0101: out = 16'h0020;
                4'b0110: out = 16'h0040;
                4'b0111: out = 16'h0080;
                4'b1000: out = 16'h0100;
                4'b1001: out = 16'h0200;
                4'b1010: out = 16'h0400;
                4'b1011: out = 16'h0800;
                4'b1100: out = 16'h1000;
                4'b1101: out = 16'h2000;
                4'b1110: out = 16'h4000;
                // BUG: Missing case for 4'b1111
                default: out = 16'h0000;  // BUG: Should be 16'h8000 for 4'b1111
            endcase
        end
    end

    // Assertions
    property one_hot_output;
        @(posedge clk) disable iff (!enable)
        $onehot(out);
    endproperty
    assert property (one_hot_output) else $error("Output is not one-hot encoded!");

    // BUG: Missing assertions for:
    // - Enable functionality
    // - Input to output delay
    // - Glitch detection
    // - Complete output coverage

endmodule 