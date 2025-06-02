// Buggy Array Multiplier

module array_multiplier #(
    parameter WIDTH = 8
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [WIDTH-1:0]     multiplicand,  // First operand
    input  logic [WIDTH-1:0]     multiplier,    // Second operand
    input  logic                 start,         // Start multiplication
    output logic [2*WIDTH-1:0]   product,       // Final product
    output logic                 done           // Multiplication complete
);

    // Internal signals
    logic [WIDTH-1:0] mcand_reg;      // Registered multiplicand
    logic [WIDTH-1:0] mplier_reg;     // Registered multiplier
    logic [WIDTH-1:0] partial_products [WIDTH-1:0];  // Partial products array
    logic [2*WIDTH-1:0] sum_array [WIDTH-1:0];      // Sum array for each row
    logic [3:0] state_counter;        // State counter for control

    // BUG: Missing proper pipeline stages
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            mcand_reg <= '0;
            mplier_reg <= '0;
            state_counter <= '0;
            done <= 1'b0;
        end else if (start) begin
            mcand_reg <= multiplicand;
            mplier_reg <= multiplier;
            state_counter <= '0;
            done <= 1'b0;
        end else if (!done) begin
            // BUG: Incorrect state counter update
            state_counter <= state_counter + 1'b1;
            if (state_counter == WIDTH-1)
                done <= 1'b1;
        end
    end

    // Partial product generation
    // BUG: Incorrect partial product generation logic
    genvar i, j;
    generate
        for (i = 0; i < WIDTH; i++) begin : pp_gen
            always_comb begin
                // BUG: Missing proper bit selection
                partial_products[i] = mplier_reg[i] ? mcand_reg : '0;
                // BUG: Should shift partial product left by i positions
            end
        end
    endgenerate

    // Addition array
    // BUG: Complex combinational logic without proper pipelining
    generate
        for (i = 0; i < WIDTH; i++) begin : sum_gen
            if (i == 0) begin
                always_comb begin
                    sum_array[i] = {{WIDTH{1'b0}}, partial_products[i]};
                end
            end else begin
                always_comb begin
                    // BUG: Incorrect shift amount in accumulation
                    sum_array[i] = sum_array[i-1] + (partial_products[i] << i);
                end
            end
        end
    endgenerate

    // Final product assignment
    // BUG: Direct combinational assignment without proper timing consideration
    always_comb begin
        product = sum_array[WIDTH-1];
    end

    // Assertions
    // BUG: Missing critical assertions for:
    // - Multiplication by 0
    // - Multiplication by 1
    // - Sign extension
    // - Overflow conditions

    property start_done_check;
        @(posedge clk) disable iff (!rst_n)
        start |-> ##[1:WIDTH+1] done;
    endproperty
    assert property (start_done_check) else $error("Multiplication not completing in time!");

    // Verification helper logic
    logic [2*WIDTH-1:0] expected_product;
    always_comb begin
        expected_product = multiplicand * multiplier;
    end

    property result_check;
        @(posedge clk) disable iff (!rst_n)
        done |-> (product == expected_product);
    endproperty
    assert property (result_check) else $error("Incorrect multiplication result!");

endmodule 