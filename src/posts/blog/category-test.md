---
title: "Verilog common questions"
category: "Interview"
date: "2020-01-28 12:00:00 +09:00"
desc: "Famous verilog interview questions"
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


