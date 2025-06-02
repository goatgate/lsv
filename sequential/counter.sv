// Buggy Up-Down Counter

module buggy_counter #(
    parameter WIDTH = 4
)(
    input  logic                clk,
    input  logic                rst_n,    // Active low reset
    input  logic                enable,   // Counter enable
    input  logic                up_down,  // 1: up, 0: down
    input  logic                load,     // Load parallel input
    input  logic [WIDTH-1:0]    data_in, // Parallel input data
    output logic [WIDTH-1:0]    count,   // Counter output
    output logic                overflow, // Overflow indicator
    output logic                underflow // Underflow indicator
);

    logic [WIDTH-1:0] next_count;
    logic             up_down_reg; // BUG: Unnecessary register causing timing issues

    // BUG: Incorrect reset implementation - should be asynchronous
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            count <= '0;
            up_down_reg <= 1'b1;
            overflow <= 1'b0;
            underflow <= 1'b0;
        end else begin
            // BUG: Missing enable check here
            up_down_reg <= up_down;
            count <= next_count;
        end
    end

    // BUG: Combinational logic sensitive to glitches
    always_comb begin
        next_count = count;
        overflow = 1'b0;
        underflow = 1'b0;

        if (load) begin
            // BUG: No synchronization with enable
            next_count = data_in;
        end else if (enable) begin
            if (up_down_reg) begin // BUG: Using registered version instead of direct input
                // BUG: Incorrect overflow detection
                if (count == '1) begin
                    next_count = '0;
                    overflow = 1'b1;
                end else begin
                    next_count = count + 1'b1;
                end
            end else begin
                // BUG: Incorrect underflow detection
                if (count == '0) begin
                    next_count = '1;
                    underflow = 1'b1;
                end else begin
                    next_count = count - 1'b1;
                end
            end
        end
    end

    // Assertions for verification
    property count_change;
        @(posedge clk) disable iff (!rst_n)
        enable |-> count != $past(count);
    endproperty
    assert property (count_change) else $error("Counter not changing when enabled");

    // BUG: Missing assertions for:
    // - Reset behavior
    // - Overflow/Underflow conditions
    // - Load functionality

endmodule 