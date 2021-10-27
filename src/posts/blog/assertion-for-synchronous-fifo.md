---
title: "Assertions for synchronous FIFO"
category: "System Verilog"
date: "2021-01-28 12:00:00 +09:00"
desc: "Assertions"
thumbnail: "./images/assertion.jpg"
alt: "apple big sur gradient"
---

## Assertions for synchronous FIFO 



<p align="center">
  <img src="./images/upf4/sync_fifo.JPG?raw=true" alt="sync_fifo"/>
</p>

```md
Scenario 1

- Check that on reset-> read_pointer=0, write_pointer=0, count=0, fifo_empty=1 and fifo_full=0 
```

```cpp
property check_reset;
@(posedge clk)
rst |-> (read_pointer===0) && (write_pointer===0) && (count===0) && (fifo_empty===1) && (fifo_full===0);
endproperty
```

```md

Scenario 2
- FIFO empty is asserted when fifo count = 0, Disable this property if reset
```

```cpp
property check_empty;
@(posedge clk) disable iff(rst)
count === 0 |-> fifo_empty;
endproperty
```

```md

Scenario 3
- FIFO full is asserted when fifo count > 7, Disable this property if reset
```


```cpp
property check_full;
@(posedge clk) disable iff(rst)
count > 7 |-> fifo_full;
endproperty
```

```md

Scenario 4
- If FIFO is full and I attempt to write, write_pointer does not change
```


```cpp
property write_pointer_stable;
@(posedge clk) disable iff(rst)
fifo_full && fifo_write && !fifo_read |-> $stable(write_pointer);
endproperty
```

```md

Scenario 5
- If FIFO is empty and I attempt to read, read_pointer does not change 
```

```cpp
property read_pointer_stable;
@(posedge clk) disable iff(rst)
fifo_empty && fifo_read && !fifo_write |-> $stable(read_pointer);
endproperty
```