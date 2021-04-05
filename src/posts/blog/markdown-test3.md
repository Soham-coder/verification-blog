---
title: "FIFO depth calculation and testplan"
category: "Questions"
date: "2020-01-28 12:00:00 +09:00"
desc: "FIFO depth calculation and testplan"
thumbnail: "./images/markdown-test3/scoreboard.png"
alt: "markdown logo"
---

## Fifo Depth Calculation (Very common and famous)


#### Theory 

```md
* Analogy-

Assume Sender is Person A
Assume Receiver is Person B
Person A can throw 10 balls at a time duration T(say).
But Person B can receive only 6 balls at the same amount of time.
As Person B cannot receive remaining 4 balls from Person A, he requires a bag or FIFO of size 10-6=4 to hold them temporarily.

Thus FIFO is used to synchronize two data rates-
Sender having higher data issuing rate communicating with receiver having lower data acceptance rate.

If sender writes 10 data in T time to FIFO and receiver reads 6 data at same time from FIFO, then FIFO depth = 10-6=4

```

```md
* Scenario-
 
Sender Frequency(clock frequency) = fs = 1/Ts
Receiver Frequency(clock frequency) = fr = 1/Tr
Sender wants to transmit M bytes of data i.e., burst size(in bytes) = M  
Delay between 2 successive writes in a burst is 1 write clock cycles i.e., sender sends 1 bytes per clock(wr clk or Ts Time)
For our example let us assume sender sends n bytes per clock(wr clk or Ts Time)
Delay between 2 successive reads in a burst is 2 read clock cycles i.e., receiver receives 1/2 bytes per clock(rd clk or Tr Time)
For our example let us assume receiver receives p bytes per clock(rd clk or Tr Time)
```

```md
* Solution-

In (1) wr clk, sender sends (n) bytes of data
=>In (Ts) time units, sender sends (n) bytes of data
=>In (Ts/n) time units, sender sends (1) byte of data
=>In ((Ts/n)*M) time units, sender sends (M) bytes of data i.e., a complete burst

In (1) rd clk, receiver can receive (p) bytes of data
=> In (Tr) time units, receiver can receive (p) bytes of data
=> In (1) time unit, receiver can receive (p/Tr) bytes of data
=> In ((Ts/n)*M) time units, receiver can receive (p/Tr)*((Ts/n)*M) bytes of data

So basically sender has send M bytes of data but receiver is only able to receive (p/Tr)*((Ts/n)*M) bytes of data in same amount of time
So FIFO depth = {M - (p/Tr)*((Ts/n)*M)} locations each containing 1 byte of data item

Thus, FIFO depth in terms of frequency = M{1-(p*fr)/(n*fs)}
where 
M = Max number of bytes that the sender can send i.e., burst size
n = Number of bytes that the sender can send per write clock
fs = Sender clock frequency
p = Number of bytes that the receiver can receive per read clock
fr = Receiver clock frequency
```

#### Problem 1
```md
* Problem 1:

Sending side-

Write clock frequency = 15MhZ
Maximum size of burst = 100 bytes
Delay b/w writes in a burst = 1 clock cycle(wr clk)

Receiving side-
Read clock frequency = 10MhZ
Delay b/w reads = 2 clock cycles(rd clk)

Calculate the depth of the FIFO.
```

```
Solution:

*  FIFO width = 8 bits(1 byte) at each buffer loaction
*  In 1 write clock, sender is able to send 1 byte of data
=> In 1/(15*10^6) sec, sender is able to send 1 byte of data
=> In 100/(15*10^6) sec, sender is able to send 100 bytes of data i.e., a complete burst
=> In 6.67us, sender is able to send 100 bytes of data

*Since delay b/w two reads is 2 read clock cycles, In 1 read clock, receiver is able to receive 1/2 bytes of data
=>In 1/(10*10^6) sec, receiver is able to receive 1/2 byte of data
=>In 1 sec, receiver is able to receive (1/2)*(10*10^6) bytes of data
=>In 6.67us, receiver is able to receive (1/2)*(10*10^6)*(6.67*10^-6) = 33.35 bytes of data

So sender has send 100 bytes of data but receiver is only able to receive 33.35 bytes of data in the same amount of time
=>FIFO Depth = 100-33.35 = 66.65 = 67(approx)

If we apply the formula directly
FIFO Depth = M{1-(p*fr)/(n*fs)}

M = 100
p = 1/2
fr = 10
n = 1
fs = 15

By putting all FIFO Depth = 100{1-(10*1/2)/(15*1)} = 100{1-1/3} = 67(approx)
```
#### Problem 2
```md
* Problem 2:

Sending side 

80 data in 100 clocks (20 data items are randomized)

Receiving Side

8 data in 10 clocks

Burst size = 160

```

```
Solution:
80 data send in 80 clocks (since 20 data items are randomized) 

Worst case is first 20 cycles idle and then [next 80 cycles write (80 data) and next also 80 cycles write(80 data)]and 20 cycles idle
So worst case writing(highest amount of writing) is 160 data in 160 clock cycles

So, 160 data send in 160 clocks

In 10 clocks receive 8 data
In 1 clock  receive 8/10 data
In 160 clocks receive ((8/10)*160)=128 data 

Depth = 160 - 128 = 32 
```
#### Question:
```md
---
How would you go about testing a normal synchronous FIFO
---
```
```md
Assumptions
Let's say depth of FIFO is 32 and width of FIFO is 16

* Reset scenario
- When the FIFO is RESET, FIFO empty flag should be set and FIFO full flag will be reset

* Non Reset scenario
- FIFO full
 - If counter == 31 and write enable is high, "almost_full" flag should be set
 - If counter == 32 "full" flag should be set
 - If 0 < counter < 31 "full" flag should be reset and "almost_full" flag should also be reset
- FIFO empty
 - If counter == 1 and read enable is high, "almost_empty" flag should be set
 - If counter == 0 "empty" flag should be set
 - If counter > 0 "empty" flag should be reset

* Normal data integrity check
- Write to n locations of FIFO and read it back and compare write vs read data
- Do simultaneous write and read to FIFO
```





