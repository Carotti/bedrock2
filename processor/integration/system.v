
`default_nettype none
`define assert(condition) if(!((|{condition})===1)) begin $display("FAIL"); $finish(1); end

module testbench; 
    reg clock=0, reset=1;
    reg [7:0] ram [0:1023];

    reg en_obtain_rq_get = 0;
    wire [64:0] obtain_rq_get;
    wire rdy_obtain_rq_get;
    reg en_send_rs_put = 0;
    reg [31:0] send_rs_put = 32'hxxxxxxxx;
    wire rdy_send_rs_put;
    mkTop mkTop(.CLK(clock),
                .RST_N(~reset),
                .EN_obtain_rq_get(en_obtain_rq_get),
                .obtain_rq_get(obtain_rq_get),
                .RDY_obtain_rq_get(rdy_obtain_rq_get),

                .send_rs_put(send_rs_put),
                .EN_send_rs_put(en_send_rs_put),
                .RDY_send_rs_put(rdy_send_rs_put)
              );
    wire [31:0] mem_rq_data = obtain_rq_get[31:0];
    wire mem_rq_iswrite = obtain_rq_get[32];
    wire [31:0] mem_rq_addr = obtain_rq_get[64:33];

    always @(*) begin
      if (rdy_obtain_rq_get && rdy_send_rs_put
          && (mem_rq_addr >> 10) == 0 && !mem_rq_iswrite)
      begin
        en_obtain_rq_get = 1;
        en_send_rs_put = 1;
        send_rs_put = {ram[mem_rq_addr+3], ram[mem_rq_addr+2], ram[mem_rq_addr+1], ram[mem_rq_addr+0]};
      end else if (rdy_obtain_rq_get && rdy_send_rs_put
          && (mem_rq_addr >> 10) == 0 && mem_rq_iswrite)
      begin
        en_obtain_rq_get = 1;
        en_send_rs_put = 1;
        ram[mem_rq_addr+0] <= mem_rq_data[7:0];
        ram[mem_rq_addr+1] <= mem_rq_data[15:8];
        ram[mem_rq_addr+2] <= mem_rq_data[23:16];
        ram[mem_rq_addr+3] <= mem_rq_data[31:24];
      end else begin
        en_obtain_rq_get = 0;
        en_send_rs_put = 0;
        // send_rs_put = 32'hxxxxxxxx;
      end
    end

    always #1 clock = !clock;
    initial begin 
      $readmemh("program.hex", ram);
      $dumpfile("system.vcd");
      $dumpvars(1, clock, reset, en_obtain_rq_get, mem_rq_iswrite, mem_rq_addr, mem_rq_data, rdy_obtain_rq_get, en_send_rs_put, send_rs_put, rdy_send_rs_put);
      #2 reset <= 0;
      #1000 $finish();
    end 
endmodule
