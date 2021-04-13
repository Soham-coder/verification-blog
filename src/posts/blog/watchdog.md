---
title: "Implementing a watchdog timer to catch hang in RTL in case of AXI transactions"
category: "Verification"
date: "2021-04-11 12:00:00 +09:00"
desc: "Watchdog Implementation"
thumbnail: "./images/watchdog/scoreboard.png"
alt: "markdown logo"
---

## Implementing a Watchdog timer to catch hang in RTL in case of AXI transactions


#### Scenario

```
* In certain cases, we encounter the following scenario while verifying slave AXI RTL IPs, which receive transactions/stimulus from corresponding master UVCs -

- This scenario mostly happens at a read transaction to slave

- At a read transaction, we encounter this scenario where master UVC has sent proper read request, but slave has not asserted the RVALID signal provided the RREADY signal from the master is always asserted i.e., the master is able to accept read data immediately

- This mostly happens at start of the verification timeline when verification engineers have got some erroneous bus signal hierarchies or that the nature of the slave addresses is ambiguous to verification engineers for the time-being i.e., (we cannot read from the particular slave addresses but it is not known to us)
```

#### Problem Statement  

```

- Now, as a verification engineer, you have already setup the environment for verification and also coded simple testcases to excercise first-hand sanity checks on the DUT, of which the majority are write followed by read to slave addresses

- But sadly some of the testcases will hang because some RTL AXI slaves will not respond to read transaction and the test will go upto timeout and it will waste your time  

- Now as a solution, you should implement a checker to catch this issue and terminate the testcase which will give you an immediate report in regression, i.e., which of the slave addresses are non responding to read ... Also, you can print the particular address of the transfer to where non-responsiveness has been encountered

- This will not only save your simulation time but is also needed by the bus design owners to correct the mistakes in the Bus RTL documents
```

#### Solution

```md
- Simple naive approach (a basic idea)

  -  We can implement a watchdog timer to catch this issue and terminate the test without moving further
```
#### Implementation

```md
We know the following for AXI Read Data Channel-

- Read data channel (AXI) 

1) The slave can assert the RVALID signal only when it drives valid read data. RVALID must remain asserted until the master accepts the data and asserts the RREADY signal. Even if a slave has only one source of read data, it must assert the RVALID signal only in response to a request for the data.

2) The master interface uses the RREADY signal to indicate that it accepts the data. The default value of RREADY can be HIGH, but only if the master is able to accept read data immediately, whenever it performs a read transaction (For our case, assume it always reamins high)

3) The slave must assert the RLAST signal when it drives the final read transfer in the burst.

We can implement the following logic in the monitor of an agent which is sampling the interface signals at each clock:

- We set the initial count value of the counter to a very high value or Timeout value
- So, when we encounter the first RVALID signal from the slave, we trigger a local event and start decrementing the counter count value
- After an event is triggered, we poll for subsequent (RVALID == 1) in a forever block
- When next RVALID comes within the set timeout, we reset the counter or restart the timer to the Timeout value
- If no RVALID comes for a time greater than the Timeout value, timeout occurs and we trigger a uvm global_event which can be accessed in testcase to drop objection and stop the uvm test
```


```cpp
//Example logic in monitor of UVM master agent "A"

class axi_monitor_MASTER_A #(int TIMEOUT=1000) extends uvm_monitor;

`uvm_component_param_utils( axi_monitor_MASTER_A #(TIMEOUT) )

//virtual interface handle

virtual axi_interface vif; 

int counter = TIMEOUT;//set counter value

event got_rvalid_high; //local event

uvm_event stop_test; //global event to stop test

//new constructor
//get vif in build phase


...

virtual task run_phase(uvm_phase phase);


...
fork 
... //Other action items or processes
poll_rvalid();
... //Other action items or processes
join

endtask : run_phase

virtual void task poll_rvalid();

forever begin //1st forever

@(posedge vif.clk);
if(vif.RVALID)
begin : rose
$display("Got RVALID first time");
-> got_rvalid_high;
break; //break from this forever loop
end : rose

end //1st forever

begin // 

wait(got_rvalid_high.triggered);
$display("Got RVALID first time at time: %0t", $time);
$display("-----ACTIVATING WATCHDOG TIMER-----");

forever begin //2nd forever

@(posedge vif.clk);

if(vif.RVALID)

begin : subsequent_RVALIDS
$display("Some more RVALIDS encountered after first RVALID @: %0t", $time);
$display("RESTARTING TIMER WITH TIMEOUT=1000");
counter <= TIMEOUT;
end : sunsequent_RVALIDS

else

begin : no_subsequent_RVALIDS
$display("No new RVALIDS encountered ... Waiting for one ... Idle observed in slave @: %0t", $time);
$display("WATCHDOG TIMER RUNNING");
counter <= counter - 1'b1;
end : no_subsequent_RVALIDS

if(counter === 0)

begin : timer_expired
$display("Timer Expired! @: %0t", $time);
$display("TERMINATING TEST_SIM");
stop_test = uvm_event_pool :: get_global("stop_test");
stop_test.trigger();
break; //break from all these loops
end : timer_expired

end //2nd forever

end//

endtask : poll_rvalid 

endclass : axi_monitor_MASTER_A

```

```cpp
//Example testcase for the master agent to catch the hang and terminate the test

class wr_MASTER_A extends axi_base_test;

`uvm_component_utils(wr_MASTER_A)

rw_seq_MASTER_A MASTER_A_seq; //take the sequence handle

uvm_event stop_test; //global uvm_event handle to catch the trigger from corresponding agent monitor

//new constructor
//build phase
...

virtual task run_phase(uvm_phase phase);

phase.raise_objection(this); //raise objection

fork : LABEL

//P1 full run upto end
begin : FULL_RUN
rw_seq_MASTER_A.start(axi_env.axi_vsqr);
end : FULL_RUN

//P2 partial run in case of hang
begin : PARTIAL_RUN
stop_test = uvm_event_pool :: get_global("stop_test");
stop_test.wait_trigger();
$display("TIMEOUT @: %0t", $time);
$display("TERMINATING TEST_SIM");
end : PARTIAL_RUN

join_any : LABEL

disable_fork; //end all running threads

`uvm_info( {get_type_name(),":run_phase"}, $sformatf("got outside fork_join @: %0t", $time), UVM_LOW );

phase.drop_objection(this); //end test



endtask : run_phase 

endclass : wr_MASTER_A
```

```md
- How to set the timeout value

In our example case, timeout = 1000

So Time of timeout = 1000*Tclk 

Check the average gap between 2 successive RVALIDs coming for a proper responsive slave = Tsucc

Set the Timeout as very much greater than Tsucc

So, (TIMEOUT_VAL*Tclk) > Tsucc + constant

```




