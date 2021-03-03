`default_nettype none
module simple_fifo #(parameter DW=8)
   (output logic [DW-1:0] data_rd,
    output logic 	  empty, full,
    input wire [DW-1:0]   data_wr,
    input wire 		  push, pop,
    input wire 		  clk, rstn);

   logic [DW-1:0] buffer [DW:0];
   logic [2:0] wrptr, rdptr;

   always_ff @(posedge clk) begin
      if (!rstn) begin
	 wrptr <= 3'h0;
	 rdptr <= 3'h0;
	 full  <= 1'b0;
	 empty <= 1'b1;
      end
      else begin
	 // Write side
	 if (push && !full) begin
`ifdef BUG2
	    wrptr <= wrptr - 1'b1;
`else
	    wrptr <= wrptr + 1'b1;
`endif
	    buffer[wrptr] <= data_wr;
	    empty <= 1'b0;
	    if (wrptr == rdptr)
`ifdef BUG1
	      full <= 1'b0;
`else
	      full <= 1'b1;
`endif
	 end
	 // Read side
	 if (pop && !empty) begin
`ifdef BUG2
	    rdptr <= rdptr - 1'b1;
`else
	    rdptr <= rdptr + 1'b1;
`endif
	    full <= 1'b0;
	    if (wrptr == rdptr)
	      empty <= 1'b1;
	 end
      end // else: !if(!rstn)
   end // always_ff @ (posedge clk)
   assign data_rd = buffer[rdptr];
   
`ifdef FORMAL
   default clocking fpv_clk @(posedge clk); endclocking
   default disable iff (!rstn);
   
   // Push and pop should not occur concurrently
   C_not_concurrent_wr_rd: assume property ($onehot({push, pop}));
   
   // BUG1
   /* Full is asserted if FIFO is full and pop is not issued. */
   ap_no_rd_then_full: assert property (full && !pop |-> ##1 full);
   
   // BUG2
   /* Write address is incremented when
    * a push is requested and fifo is not full. */
   let max_wraddr_count = &wrptr;
   ap_accept_write: assert property (!max_wraddr_count && !full && push |-> ##1 !$stable(wrptr));
   /* Read address is incremented when
    * a pop is requested and fifo is not empty. */
   let max_rdaddr_count = &rdptr;
   ap_accept_read: assert property (!max_rdaddr_count && !empty && pop |-> ##1 !$stable(rdptr));
`endif //  `ifdef FORMAL
   
`ifdef WITNESS
   // BUG1
 `ifdef BUG1
   WITNESS_no_rd_then_full: assert property (full && !pop ##1 full);
 `endif
   
   // BUG2
 `ifdef BUG2
   WITNESS_ap_accept_write: assert property (not ((!max_rdaddr_count && !empty && pop ##1 !$stable(rdptr))));
   WITNESS_ap_accept_read:  assert property (not ((!max_rdaddr_count && !empty && pop ##1 !$stable(rdptr)))); 
 `endif
`endif //  `ifdef WITNESS
endmodule // simple_fifo
