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
 c = a; //LHS will be eavaluated in active region and RHS will be updated in active region. So c will get value a as well as b will also get value a if they are printed by system task $display. It will synthesize to only 1 flop with a as input and b=c as output with clk
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
 c <= a;//LHS will be evaluated in active region and RHS will be updated in NBA region. So c will get value of a, and b will get value of c if they are printed by system task $strobe which occurs at the NBA region. It will synthesize to 2 f/fs - 1st flop with i/p as a and o/p as c - 2nd flop with i/p as c and o/p as b, both clocked by the same clock "clk"
 b <= c; //This also leads to addition of pipeline registers where we put registers or f/fs in critical path i.e., longest combinational loop to break it down into shorter sequential paths
end
```

```md
---
Q2: Frequency divider or clock divider by 2
---
```

```md
For the circuit-

We have a f_f with input d and output q and ~q clocked by clock "clk" which needs to be divided. If you connect ~q with input d then the output q will be your desired output
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


