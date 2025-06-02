// Buggy Traffic Light Controller

module traffic_light_controller (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        emergency,    // Emergency vehicle signal
    input  logic        pedestrian,   // Pedestrian crossing request
    input  logic        sensor_ns,    // North-South traffic sensor
    input  logic        sensor_ew,    // East-West traffic sensor
    output logic [2:0]  lights_ns,    // North-South {RED, YELLOW, GREEN}
    output logic [2:0]  lights_ew,    // East-West {RED, YELLOW, GREEN}
    output logic        walk_ns,      // North-South walk signal
    output logic        walk_ew       // East-West walk signal
);

    // State encoding
    // BUG: Poor state encoding choice leading to potential glitches
    typedef enum logic [2:0] {
        NS_GREEN  = 3'b000,
        NS_YELLOW = 3'b001,
        NS_RED    = 3'b010,
        EW_GREEN  = 3'b011,
        EW_YELLOW = 3'b100,
        ALL_RED   = 3'b101,
        EMERGENCY = 3'b110
        // BUG: Missing PEDESTRIAN state (3'b111)
    } state_t;

    state_t current_state, next_state;
    logic [4:0] timer;  // 5-bit timer for state transitions
    logic timer_done;

    // Timer logic
    // BUG: Incorrect timer implementation
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            timer <= 5'd0;
        end else if (timer_done) begin
            timer <= 5'd0;
        end else begin
            timer <= timer + 1'b1;
        end
    end

    // BUG: Incorrect timer threshold for different states
    assign timer_done = (timer == 5'd20);

    // State register
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            current_state <= NS_GREEN;
        end else begin
            current_state <= next_state;
        end
    end

    // Next state logic
    // BUG: Complex combinational logic with potential timing issues
    always_comb begin
        next_state = current_state; // Default assignment

        case (current_state)
            NS_GREEN: begin
                if (emergency) begin
                    next_state = EMERGENCY;
                end else if (timer_done && !sensor_ns) begin
                    next_state = NS_YELLOW;
                end
                // BUG: Missing pedestrian handling
            end

            NS_YELLOW: begin
                if (emergency) begin
                    next_state = EMERGENCY;
                end else if (timer_done) begin
                    next_state = NS_RED;
                end
            end

            NS_RED: begin
                // BUG: Direct transition without ALL_RED state
                next_state = EW_GREEN;
            end

            EW_GREEN: begin
                if (emergency) begin
                    next_state = EMERGENCY;
                end else if (timer_done && !sensor_ew) begin
                    next_state = EW_YELLOW;
                end
            end

            EW_YELLOW: begin
                if (emergency) begin
                    next_state = EMERGENCY;
                end else if (timer_done) begin
                    next_state = ALL_RED;
                end
            end

            ALL_RED: begin
                if (emergency) begin
                    next_state = EMERGENCY;
                end else if (timer_done) begin
                    next_state = NS_GREEN;
                end
            end

            EMERGENCY: begin
                // BUG: Deadlock condition - no exit from emergency state
                if (emergency) begin
                    next_state = EMERGENCY;
                end
            end

            default: next_state = NS_GREEN;
        endcase
    end

    // Output logic
    // BUG: Combinational output without registered outputs
    always_comb begin
        // Default assignments
        lights_ns = 3'b100; // RED
        lights_ew = 3'b100; // RED
        walk_ns = 1'b0;
        walk_ew = 1'b0;

        case (current_state)
            NS_GREEN: begin
                lights_ns = 3'b001; // GREEN
                // BUG: Walk signal timing issue
                walk_ns = pedestrian;
            end

            NS_YELLOW: begin
                lights_ns = 3'b010; // YELLOW
            end

            EW_GREEN: begin
                lights_ew = 3'b001; // GREEN
                // BUG: Walk signal timing issue
                walk_ew = pedestrian;
            end

            EW_YELLOW: begin
                lights_ew = 3'b010; // YELLOW
            end

            EMERGENCY: begin
                // BUG: Incorrect emergency handling
                lights_ns = 3'b100; // RED
                lights_ew = 3'b100; // RED
            end

            default: begin
                lights_ns = 3'b100; // RED
                lights_ew = 3'b100; // RED
            end
        endcase
    end

    // Basic assertion
    property no_green_conflict;
        @(posedge clk) disable iff (!rst_n)
        !(lights_ns[0] && lights_ew[0]);
    endproperty
    assert property (no_green_conflict) else $error("Both directions show GREEN!");

    // BUG: Missing critical assertions for:
    // - Proper yellow timing
    // - Pedestrian signal safety
    // - Emergency vehicle handling
    // - Proper state transitions

endmodule 