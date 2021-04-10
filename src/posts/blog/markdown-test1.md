---
title: "Development of a pipelined driver"
category: "Verification"
date: "2020-01-28 12:00:00 +09:00"
desc: "Development of a pipelined driver"
thumbnail: "./images/markdown-test1/thumbnail.jpg"
alt: "markdown logo"
---

## Coding Scenario 


#### Question 
```md
---
Q4: Develop a driver for the following scenario(write basic idea code for the drive task only)

Transaction have addr and data fields
Timing diagram is similar as below - pipelined data and addresses

**Time** - T1     |   T1+5   |   T2
**ADDR** - addr1  |   addr2
**DATA** -            data1  |  data2
```

```cpp
//A simple way to model a pipelined protocol with a sequence and driver is to use the get() and put() methods from the driver-sequencer API.
//Official solution
class driver extends uvm_driver#(transaction);

...

virtual task run_phase(uvm_phase phase);

fork
pipelined_drive_items();
join

endtask : run_phase




semaphore lock = new(1); //1 key is present to function 1 phase at a time 



event data_phase_starting;
transaction current_tr_q[$]; //take a queue to maintain current tr

virtual void task automatic pipelined_drive_items();

transaction req;

forever begin
seq_item_port.get(req);
accept_tr(req, $time);
void'(begin_tr(req, "driver"));
addr_phase();
    // This blocking call performs the addr phase of the request and then returns
    // right away before completing the data phase, thus allowing the addr phase 
    // of the subsequent request (next loop iteration) to occur in parallel with the 
    // data phase of the current request, and so implementing the pipeline
current_tr_queue.push_back(req);
end
endtask : pipelined_drive_items

//Semaphore is used to maintain so that no more than 1 transaction enters each pipe stage i.e., addr and data
task addr_phase(transaction req);
//begin addr phase
@(posedge vif.clk);
vif.addr <= req.addr;
lock.get(1); //get a key at start of data phase .i.e., lock the pipeline
-> data_phase_starting; //trigger event to start data_phase and immediately return back to seq_item_port get method without blocking and bring another req
endtask : addr_phase


always begin //always executing
@(data_phase_starting);
repeat(5)@(posedge vif.clk);
vif.data <= req.data;
transaction rsp = current_tr_queue.pop_front();
rsp.copy(req);
seq_item_port.put(rsp);
end_tr(rsp);
lock.put(1); //put the key to release the pipeline at end of data phase
end

endclass : driver
```

```cpp
//Another solution
//This is untested!! but intuitive
typedef mailbox#(transaction) mbox; 
class driver extends uvm_driver#(transaction);

... 

//Mailbox has blocking methods so will maintain synchronisation
mbox addr_mbox;
mbox data_mbox
transaction tr;

virtual task run_phase(uvm_phase phase);

fork 
addr();
data();
join_none //It will get out immediately and bring out next seq_item

forever begin
seq_item_port.get_next_item(tr);
seq_item_port.item_done(); //Item done called immediately because driver's job is over. Remaining will be done by the 'addr' and 'data' parallel threads
addr_mbox.put(tr);//put the tr to address phase mailbox
end
endtask:run_phase

task addr();
forever begin
transaction addr_phase;
addr_mbox.get(addr_phase);

//drive the addr
@(posedge vif.clk);
vif.addr <= addr_phase.addr;
data_mbox.put(addr_phase); //put the tr to data phase mailbox
end
endtask:addr

task data();
forever begin
transaction data_phase;
data_mbox.get(data_phase);
repeat(5)@(posedge vif.clk);
vif.data <= data_phase.data;
...
end
endtask:data

endclass: driver
```

```cpp
//In case if you are not able to give any of these solutions accurately, below may also work depending on interviewer which is similar or close to actual solution

class driver extends uvm_driver#(transaction);

...
event data_phase_start;
transaction current_req[$];

virtual task run_phase();
forever begin

seq_item_port.get_next_item(req);

drive_items(req);

seq_item_port.item_done();

end
endtask: run_phase

void task drive_items(req);

fork
addr_phase(req);
data_phase(req);
join_none //It will immediately get out and call item_done() and get next sequence_item

void task addr_phase(transaction req);

@(posedge vif.clk);
vif.addr <= req.addr;
current_req.push_back(req);
-> data_phase_start;
endtask: addr_phase

void task data_phase(transaction req);
@(data_phase_start.triggered);
current_req.pop_front(req);
repeat(5)@(posedge vif.clk);
vif.data <= req.data;
endtask: data_phase

endclass:driver

//But this solution still have possibilty of having more than 1 txs in 1 phase. So add semaphores and lock pipe before starting data phase
//and release pipe after finishing data phase as solution 1 
```











