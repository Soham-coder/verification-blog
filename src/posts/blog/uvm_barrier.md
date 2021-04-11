---
title: "UVM barrier and it's usage"
category: "Verification"
date: "2021-04-11 12:00:00 +09:00"
desc: "UVM barrier and it's usage"
thumbnail: "./images/uvm_barrier/scoreboard.png"
alt: "markdown logo"
---

## Barrier in UVM and Usage of uvm_barrier


#### Theory 

```md
1) uvm_barrier can be used to force a set of independently executing processes (eg., virtual sequences)
to wait until they have reached a particular threshold point.
The barrier provides a flexible synchronization mechanism between the processes.

2) It's threshold can be programmed to set the number of processes that must reach the synchronization
or completion point before the barrier is lifted.

3) A barrier simply blocks others until a threshold number of requests.

4) Thus the uvm_barrier class provides a multi-process synchronization mechanism. It enables a set of 
processes to block until the desired number of processes get to the synchronization point, after which
all the blocked processes are released.
```
```md
Some APIs of uvm_barrier class - 

1) wait_for (most used) : Waits for enough processes to reach the barrier before continuing
2) reset : Resets the barrier. This sets the waiter count back to 0
3) set_auto_reset : Determines if the barrier should reset itself after the threshold is reached
                    Default value is 1
4) set_threshold : Sets the process threshold
5) get_threshold : Gets the current threshold setting for the barrier
6) get_num_waiters : Returns the number of processes currently blocked by the barrier
7) cancel : Decrements the waiter count by 1
            This is used when a process that was waiting/blocked on the barrier is killed or activated by some means
```
```cpp
//Let us consider an eg., code

module top();

import uvm_pkg::*;

uvm_barrier b; //declare uvm_barrier handle

task delay //utility task to set a time consuming process 
(
input uvm_barrier b,
input unsigned delay, //cannot be negative
input string process_name
);
 
automatic string s = process_name; 
//process_name will be changed for every processes and everytime this task is invoked

#delay; //time consumed by process

b.wait_for(); //wait for the barrier to be uplifted

$display("%s Process at %0t", s, $realtime);

endtask : delay

initial begin//

b = new("Barrier",2); //Wait for 2 processes to come to completion/synchronization point

fork:LABEL
	
	delay(.b(b), .delay(10), .process_name("A"); //call "A" process
	delay(.b(b), .delay(35), .process_name("B"); //call "B" process
	delay(.b(b), .delay(50), .process_name("C"); //call "C" process
	delay(.b(b), .delay(20), .process_name("D"); //call "D" process
	delay(.b(b), .delay(80), .process_name("E"); //call "E" process
	delay(.b(b), .delay(70), .process_name("F"); //call "F" process
        
join:LABEL

	$display("Came out of fork_join at %0t", $realtime);
end//

endmodule : top
```
```
So in this case the output barrier will be -> max{any 2 current processes waiting on the barrier and having lowest time delay}

Out of {"A","D"} 
"D" finishes at 20, so "A" will be blocked till 20

Next...
Out of {"B", "C"}
"C" finishes at 50, so "B" will be blocked till 50

Next...
Out of {"F", "E"}
"E" finishes at 80, so "F" will be blocked till 80

So print statements will be as below:
 // A Process at 20
 // D Process at 20
 // B Process at 50
 // C Process at 50
 // F Process at 80
 // E Process at 80
 // Came out of fork_join at 80

  
```

```
...Similarly you can try for other egs., where you wait for 3 or more processes for barrier to be
uplifted
``` 





