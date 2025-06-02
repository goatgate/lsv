// Buggy 8:1 Multiplexer

module buggy_mux #(
    parameter WIDTH = 8
)(
    input  logic              clk,          // Clock for timing analysis
    input  logic              rst_n,        // Active low reset
    input  logic [WIDTH-1:0]  data_in [8],  // 8 input buses
    input  logic [2:0]        select,       // 3-bit select input
    input  logic              enable,       // Active high enable
    output logic [WIDTH-1:0]  data_out      // Selected output
);

    logic [WIDTH-1:0] data_reg [8];    // BUG: Unnecessary input registers
    logic [2:0]       select_reg;      // BUG: Unnecessary select register
    logic             enable_reg;      // BUG: Unnecessary enable register

    // BUG: Unnecessary sequential logic for combinatorial multiplexer
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < 8; i++) begin
                data_reg[i] <= '0;
            end
            select_reg <= '0;
            enable_reg <= '0;
        end else begin
            for (int i = 0; i < 8; i++) begin
                data_reg[i] <= data_in[i];
            end
            select_reg <= select;
            enable_reg <= enable;
        end
    end

    // BUG: Complex priority logic instead of simple multiplexing
    always_comb begin
        data_out = '0;  // Default assignment

        // BUG: Wrong enable logic implementation
        if (enable_reg) begin  // Should check enable directly
            // BUG: Using registered signals instead of direct inputs
            unique case (1'b1)  // BUG: Should use select directly
                (select_reg == 3'b000): data_out = data_reg[0];
                (select_reg == 3'b001): data_out = data_reg[1];
                (select_reg == 3'b010): data_out = data_reg[2];
                (select_reg == 3'b011): data_out = data_reg[3];
                (select_reg == 3'b100): data_out = data_reg[4];
                (select_reg == 3'b101): data_out = data_reg[5];
                (select_reg == 3'b110): data_out = data_reg[6];
                (select_reg == 3'b111): data_out = data_reg[7];
                default: data_out = 'x;  // BUG: Should maintain last valid output
            endcase
        end
    end

    // Assertions
    property valid_select;
        @(posedge clk) disable iff (!rst_n)
        enable |-> (data_out == data_in[select]);
    endproperty
    assert property (valid_select) else $error("Invalid output selection!");

    // BUG: Missing assertions for:
    // - Enable functionality
    // - Reset behavior
    // - Glitch detection
    // - X-value propagation

endmodule 