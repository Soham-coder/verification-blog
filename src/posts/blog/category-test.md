---
title: "Verilog common questions"
category: "Questions"
date: "2020-01-28 12:00:00 +09:00"
desc: "Famous verilog questions"
thumbnail: "./images/default.jpg"
alt: "apple big sur gradient"
---

## Verilog famous questions

```md
---
Q1: Difference b/w blocking and non-blocking statements 
---
```
```cpp

module blocking_ff(clk, a, b);

input clk;
input a;
output b;
reg c;
always_ff@(posedge clk)
begin
 c = a; //LHS will be evaluated in active region and RHS will be updated in active region. So c will get value a as well as b will also get value a .Their values will get reflected if printed by system task $display or $strobe. It will synthesize to only 1 flip-flop with a as input and b=c as output with "clk" as clock of the flip-flop
 b = c;
end
```
```cpp
module non_blocking_ff(clk, a, b);

input clk;
input a;
output b;
reg c;
always_ff@(posedge clk)
begin
 c <= a;//LHS will be evaluated in active region and RHS will be updated in NBA region. So c will get value of a, and b will get value of c
 //Their values will be reflected if they are printed by system task $strobe which occurs at the NBA region. 
 //It will synthesize to 2 f/fs - 1st flop with i/p as a and o/p as c
 //2nd flop with i/p as c and o/p as b, both clocked by the same clock "clk"
 b <= c; 
 //This is also the way for addition of pipeline registers where we put registers or f/fs in critical path i.e., longest combinational loop to break it down into shorter sequential paths
end
```

```md
---
Q2: Frequency divider or clock divider by 2
---
```

```md
For the circuit-

We have a flip-flop with input d and output q and ~q clocked by clock "clk"
//The input clk needs to be divided by 2 
//So if you connect output ~q with input d then the normal output q 
//will act as your divided_by_2 clock
```
```cpp
module freq_divider_by_2(rst, clk, clk_by_2);

input rst;
input clk;
output reg clk_by_2;

//q = clk_by_2
//~q = ~clk_by_2

always_ff@(posedge clk)
begin
if(rst)//high active rst (say)
clk_by_2 <= 1'b0;
else
clk_by_2 <= ~clk_by_2; //connect the q~ to d
end

endmodule
```              

```md
---
Q3: Draw a state machine for a sequence detector which can detect the pattern 1010 [01*] 0111

[01*] means that any number of 0s followed by any number of 1s
eg., 00..1, 0111.., 01, 001, 011, 1, 1.., 11 etc., 
---
```
```md
*Disclaimer- I have not faced this type of question before where sequence can be multiple combinations - So please do point out if you see any flaw or states that have not been considered*
*Error Note- In figure transition should be S8 --> S2 (0/0) !!!*
```


#### State Diagram
![State Diagram](./images/category-test/state_dia.png)


```cpp

module sd1010_any0any1_0111_mealy
(
    clk,
    reset,
    data_in,
    data_out
);

input clk;
input reset;
input data_in;
output data_out;

typedef enum logic[3:0] 
{
    IDLE = 0
    S0 = 1, 
    S1 = 2,
    S2 = 3,
    S3 = 4,
    S4 = 5,
    S5 = 6,
    S6 = 7,
    S7 = 8,
    S8 = 9,
    S9 = 10
}
state_t;

(* fsm_encoding = "grey" *)    state_t current_state;
(* fsm_encoding = "grey" *)    state_t next_state;

//Automatically synthesis tool will encode states into optimized grey encoding format

//Current state logic (sequential)

always_ff @ (posedge clk, posedge reset)
begin//
if(reset)
    current_state <= IDLE;
else
    current_state <= next_state;
end//

//Next state logic (combinational)

always_comb

begin//

next_state = current_state; //default is to stay in current state

unique_case (current_state)
    
    IDLE :  ( data_in) ? next_state = S0 : IDLE  ;
    
    S0   :  ( data_in) ? next_state = S1 : S0    ;
    S1   :  (!data_in) ? next_state = S2 : S1    ;
    S2   :  ( data_in) ? next_state = S3 : S0    ;
    S3   :  (!data_in) ? next_state = S4 : S1    ;

    S4   :  (!data_in) ? next_state = S5 : S6    ;
    S5   :  ( data_in) ? next_state = S6 : S5    ;
    
    S6   :  (!data_in) ? next_state = S7 : S6    ;
    S7   :  ( data_in) ? next_state = S8 : S0    ;
    S8   :  ( data_in) ? next_state = S9 : S2    ; //010 is done so expecting a 10 for overlapped case. Jump to S2
    // In figure transition should be S8 --> S2 (0/0) !
    S9   :  ( data_in) ? next_state = S0 : S2    ; //0110 is done so expecting a 10 for overlapped case. Jump to S2

endcase

end//

//Output assignment
assign data_out = (current_state == S9) ? 1 : 0;

endmodule


```