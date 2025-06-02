// Buggy FIFO

module buggy_fifo #(
    parameter WIDTH = 8,
    parameter DEPTH = 16
)(
    input  logic              clk,
    input  logic              rst_n,
    input  logic              write_en,
    input  logic              read_en,
    input  logic [WIDTH-1:0]  data_in,
    output logic [WIDTH-1:0]  data_out,
    output logic              full,
    output logic              empty,
    output logic              overflow,
    output logic              underflow
);

    localparam ADDR_WIDTH = $clog2(DEPTH);

    // Memory array
    logic [WIDTH-1:0] mem [DEPTH];

    // Pointers and counters
    logic [ADDR_WIDTH:0] write_ptr;  // Extra bit for full detection
    logic [ADDR_WIDTH:0] read_ptr;   // Extra bit for empty detection
    logic [ADDR_WIDTH:0] count;      // Number of entries

    // BUG: Incorrect pointer synchronization
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            write_ptr <= '0;
            read_ptr <= '0;
            count <= '0;
            overflow <= 1'b0;
            underflow <= 1'b0;
        end else begin
            // BUG: Missing write_en check before incrementing write_ptr
            if (write_en) begin
                write_ptr <= write_ptr + 1'b1;
            end

            // BUG: Missing read_en check before incrementing read_ptr
            if (read_en) begin
                read_ptr <= read_ptr + 1'b1;
            end

            // BUG: Incorrect counter update logic
            if (write_en && !read_en) begin
                count <= count + 1'b1;
            end else if (!write_en && read_en) begin
                count <= count - 1'b1;
            end
        end
    end

    // BUG: Incorrect full/empty detection
    assign full = (count == DEPTH);  // Should compare write_ptr and read_ptr
    assign empty = (count == 0);     // Should compare write_ptr and read_ptr

    // BUG: Missing overflow/underflow protection
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            overflow <= 1'b0;
            underflow <= 1'b0;
        end else begin
            // BUG: Incorrect overflow detection
            if (write_en && full) begin
                overflow <= 1'b1;
            end
            // BUG: Incorrect underflow detection
            if (read_en && empty) begin
                underflow <= 1'b1;
            end
        end
    end

    // Memory write
    // BUG: Missing write protection
    always_ff @(posedge clk) begin
        if (write_en) begin
            mem[write_ptr[ADDR_WIDTH-1:0]] <= data_in;
        end
    end

    // Memory read
    // BUG: Combinational read output
    assign data_out = mem[read_ptr[ADDR_WIDTH-1:0]];

    // Assertions
    property no_write_when_full;
        @(posedge clk) disable iff (!rst_n)
        full |-> !write_en;
    endproperty
    assert property (no_write_when_full) else $error("Write attempted when FIFO full!");

    property no_read_when_empty;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !read_en;
    endproperty
    assert property (no_read_when_empty) else $error("Read attempted when FIFO empty!");

    // BUG: Missing assertions for:
    // - Pointer wrap-around
    // - Data integrity
    // - Reset behavior
    // - Full/empty flag timing
    // - Overflow/underflow conditions

endmodule 