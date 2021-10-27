---
title: "Assertions for up-down counter"
category: "System Verilog"
date: "2021-01-28 12:00:00 +09:00"
desc: "Assertions"
thumbnail: "./images/assertion.jpg"
alt: "apple big sur gradient"
---

## Assertions for up-down counter 



<p align="center">
  <img src="./images/upf4/updwn_counter.JPG?raw=true" alt="counter"/>
</p>

```md
Scenario 1

- Check that on reset, data_out = 0 
```

```cpp
property check_reset;
@(posedge clk)
rst |-> data_out === 0;
endproperty
```

```md
Scenario 2

- If load_count is deasserted and count_enable = 0(i.e., counting is not enabled), data_out holds its' previous value
```

```cpp
property check_hold;
@(posedge clk) disable iff(rst)
!load_count && !count_enable |-> data_out === $past(data_out);
endproperty
```


```md

Scenario 3
- If load count is deasserted and count_enable = 1(i.e., counting is enabled), if updwn_cnt = 1, the count goes up and if updwn_cnt = 0, the count goes down 
```


```cpp
property check_count;
@(posedge clk) disable iff(rst)
!load_count && count_enable |->
if(updwn_count)
##1
data_out === $past(data_out) + 1
else
##1
data_out === $past(data_out) - 1;
endproperty

```