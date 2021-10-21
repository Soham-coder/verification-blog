---
title: "Assertions for asynchronous FIFO"
category: "System Verilog"
date: "2021-01-28 12:00:00 +09:00"
desc: "Assertions"
thumbnail: "./images/assertion.jpg"
alt: "apple big sur gradient"
---

## Assertions for asynchronous FIFO 



<p align="center">
  <img src="./images/upf4/async_fifo.JPG?raw=true" alt="async_fifo"/>
</p>

```md
Scenario 1

- If FIFO is empty, read_pointer does not change
```

```cpp
property check_empty;
@(posedge rclk) disable iff(rclk_rst)
fifo_empty |-> @(posedge rclk) 
if(!unknown($past(read_pointer)))
read_pointer === $past(read_pointer); 
endproperty
```

```md

Scenario 2
- If FIFO is full, write_pointer does not change
```

```cpp
property check_full;
@(posedge wclk) disable iff(wclk_rst)
fifo_full |-> @(posedge wclk) write_pointer === $past(write_pointer);
endproperty
```

```md

Scenario 3
- Check that data that is read when read_pointer reaches write_pointer is same as the data that is written at the write_pointer
```

```cpp

sequence read_detect(pointer);
##[0:$] (fifo_read && !fifo_empty && read_pointer === pointer); 
endsequence

property write_read_data_integrity_check;

integer pointer, data;

@(posedge wclk) disable iff (wclk_rst) || (rclk_rst)

fifo_write && !fifo_full, data = fifo_data_in, pointer = write_pointer)
->
@(posedge rclk) first_match(read_detect(pointer)) 

##0

fifo_data_out === data;

endproperty
```