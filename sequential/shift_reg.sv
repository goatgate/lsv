// Buggy Shift Register

module buggy_shift_reg #(
    parameter WIDTH = 8
)(
    input  logic              clk,
    input  logic              rst_n,
    input  logic              shift_en,     // Shift enable
    input  logic              load_en,      // Parallel load enable
    input  logic              direction,    // 1: right, 0: left
    input  logic              serial_in,    // Serial input
    input  logic [WIDTH-1:0]  parallel_in,  // Parallel input
    output logic [WIDTH-1:0]  parallel_out, // Parallel output
    output logic              serial_out    // Serial output
);

    logic [WIDTH-1:0] shift_reg;
    logic direction_reg;  // BUG: Unnecessary direction register

    // BUG: Incorrect reset implementation
    always_ff @(posedge clk) begin  // Should be async reset
        if (!rst_n) begin
            shift_reg <= '0;
            direction_reg <= 1'b0;
        end else begin
            direction_reg <= direction;  // BUG: Unnecessary registration
            
            // BUG: Priority logic is reversed
            if (load_en) begin
                // BUG: Data corruption during load
                shift_reg <= parallel_in & {WIDTH{shift_en}};  // Should be just parallel_in
            end else if (shift_en) begin
                if (direction_reg) begin  // BUG: Using registered direction
                    // Right shift
                    // BUG: Incorrect shift implementation
                    shift_reg <= {serial_in, shift_reg[WIDTH-1:0]};  // Wrong bit selection
                end else begin
                    // Left shift
                    // BUG: Incorrect shift implementation
                    shift_reg <= {shift_reg[WIDTH-2:0], serial_in};  // Wrong bit selection
                end
            end
        end
    end

    // BUG: Combinational output logic without registration
    always_comb begin
        parallel_out = shift_reg;
        serial_out = direction_reg ? shift_reg[0] : shift_reg[WIDTH-1];
    end

    // Assertions
    property load_check;
        @(posedge clk) disable iff (!rst_n)
        load_en |=> (parallel_out == parallel_in);
    endproperty
    assert property (load_check) else $error("Parallel load failed!");

    // BUG: Missing assertions for:
    // - Shift operation verification
    // - Direction control
    // - Reset value checking
    // - Serial input/output verification
    // - Enable signal functionality

    // Helper logic for verification
    logic [WIDTH-1:0] expected_right_shift;
    logic [WIDTH-1:0] expected_left_shift;

    always_comb begin
        expected_right_shift = {serial_in, shift_reg[WIDTH-1:1]};
        expected_left_shift = {shift_reg[WIDTH-2:0], serial_in};
    end

endmodule 