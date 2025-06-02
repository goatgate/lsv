// Buggy Wallace Tree Multiplier

module wallace_multiplier #(
    parameter WIDTH = 8
)(
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 start,         // Start multiplication
    input  logic [WIDTH-1:0]     multiplicand,  // First operand
    input  logic [WIDTH-1:0]     multiplier,    // Second operand
    output logic [2*WIDTH-1:0]   product,       // Final product
    output logic                 done           // Multiplication complete
);

    // Internal signals
    logic [WIDTH-1:0] mcand_reg;
    logic [WIDTH-1:0] mplier_reg;
    logic [WIDTH-1:0] partial_products [WIDTH];
    logic [2*WIDTH-1:0] sum_level1 [WIDTH/2];
    logic [2*WIDTH-1:0] carry_level1 [WIDTH/2];
    logic [2*WIDTH-1:0] sum_level2 [WIDTH/4];
    logic [2*WIDTH-1:0] carry_level2 [WIDTH/4];
    logic [2*WIDTH-1:0] final_sum;
    logic [2*WIDTH-1:0] final_carry;

    // Control signals
    logic processing;
    logic [2:0] stage_counter;

    // BUG: Incorrect state handling
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            processing <= 1'b0;
            stage_counter <= '0;
            done <= 1'b0;
        end else begin
            if (start && !processing) begin
                processing <= 1'b1;
                stage_counter <= '0;
                done <= 1'b0;
            end else if (processing) begin
                if (stage_counter == 3'b100) begin
                    processing <= 1'b0;
                    done <= 1'b1;
                end else begin
                    stage_counter <= stage_counter + 1'b1;
                end
            end else begin
                done <= 1'b0;
            end
        end
    end

    // Input registers
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            mcand_reg <= '0;
            mplier_reg <= '0;
        end else if (start && !processing) begin
            mcand_reg <= multiplicand;
            mplier_reg <= multiplier;
        end
    end

    // Partial product generation
    // BUG: Incorrect partial product generation
    genvar i, j;
    generate
        for (i = 0; i < WIDTH; i++) begin : pp_gen
            always_comb begin
                partial_products[i] = mplier_reg[i] ? mcand_reg : '0;
                // BUG: Missing shift operation
                // Should be: partial_products[i] = (mplier_reg[i] ? mcand_reg : '0) << i;
            end
        end
    endgenerate

    // First level reduction
    // BUG: Incorrect carry propagation
    generate
        for (i = 0; i < WIDTH/2; i++) begin : level1
            always_ff @(posedge clk) begin
                if (processing && stage_counter == 0) begin
                    {carry_level1[i], sum_level1[i]} = 
                        partial_products[2*i] + 
                        partial_products[2*i+1];
                    // BUG: Missing carry from previous stage
                end
            end
        end
    endgenerate

    // Second level reduction
    // BUG: Timing violations in reduction tree
    generate
        for (i = 0; i < WIDTH/4; i++) begin : level2
            always_ff @(posedge clk) begin
                if (processing && stage_counter == 1) begin
                    {carry_level2[i], sum_level2[i]} = 
                        sum_level1[2*i] + 
                        sum_level1[2*i+1] + 
                        (carry_level1[2*i] << 1) +
                        (carry_level1[2*i+1] << 1);
                    // BUG: Incorrect carry shift
                end
            end
        end
    endgenerate

    // Final addition stage
    // BUG: Missing pipeline stage
    always_ff @(posedge clk) begin
        if (processing && stage_counter == 2) begin
            {final_carry, final_sum} = sum_level2[0] + (carry_level2[0] << 1);
            // BUG: Incorrect final addition
        end
    end

    // Output assignment
    // BUG: Incorrect product selection
    always_ff @(posedge clk) begin
        if (processing && stage_counter == 3) begin
            product <= final_sum;  // Should consider final_carry
        end
    end

    // Assertions
    property valid_multiplication;
        @(posedge clk) disable iff (!rst_n)
        done |-> (product == (multiplicand * multiplier));
    endproperty
    assert property (valid_multiplication) else $error("Incorrect multiplication result!");

    // BUG: Missing assertions for:
    // - Partial product verification
    // - Carry propagation checking
    // - Pipeline stage timing
    // - Overflow detection
    // - Control signal sequencing

    // Helper logic for verification
    logic [2*WIDTH-1:0] expected_product;
    always_comb begin
        expected_product = multiplicand * multiplier;
    end

endmodule 