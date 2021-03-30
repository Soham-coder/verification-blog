---
title: "SV questions"
category: "Questions"
date: "2020-01-28 12:00:00 +09:00"
desc: "SV problem solving questions"
thumbnail: "./images/getting-started/thumbnail.jpg"
alt: "apple and shaking hands"
---

## Some SV problem solving questions

#### Question1
```md
---
Q1: 3 parallel processes are there. Write a SV code such that after any 2 processes finish, you come out of the threads and end execution
---
```

```cpp
//Method 1 by use of disable_fork 
class abc;

process process1, process2, process3;

fork : LABEL
begin
process1 = process::self();
process2 = process::self();
process3 = process::self();
end 
join_none
if(process1.status === process::FINISHED && process2.status === process::FINISHED) || (process1.status === process::FINISHED && process3.status === process::FINISHED) || (process2.status === process::FINISHED && process3.status === process::FINISHED)
disable_fork : LABEL
endclass : abc
```
```cpp
//Method 2 by use of semaphore

class abc;
semaphore s;
process process1, process2, process3;

//initialise semaphore with 0 key
function new();
s = new(0);
endfunction:new

task multiple_process();
fork
//process 1 ( within 1 begin-end will be treated as 1 process, execute sequentially)
begin
process1 = process::self();
s.put(1);
end
//process 2
begin
process2 = process::self();
s.put(1);
end
//process 3
begin
process3 = process::self();
s.put(1);
end

join_none
s.get(2); //when you get 2 keys end execution
disable_fork;
s = null; //remove semaphore

endtask : multiple_process
endclass : abc
```
```cpp
//method 3 by use of wait statements
class abc;
process process1, process2, process3;

int count; 

task multiple_process();
fork 

begin
//P1
process1 = process :: self();
count++;
end

begin
//P2
process2 = process :: self();
count++;
end

begin
//P3
process3 = process :: self();
count++;
end


join_none

wait(count === 2); //level sensitive

disable_fork;
endtask : multiple_process


endclass : abc
```

#### Question2
```md
---
Q2: There is a signal wdata[63:0] representing data-bus 
    There is a signal wstrb[7:0] representing strobe/valid byte of the data-bus

When a valid byte is present in wdata, it has to be either 8'b11111111 or 8'b10101010
Write a SV code/constraint to generate suitable transactions
---
```

```cpp
class abc;
rand bit [7:0] wstrb;
rand bit [63:0] wdata;
rand bit [7:0] valid_byte;

constraint valid_byte { valid_byte inside {8'b11111111,8'b10101010};}
constraint valid_wdata { foreach(wstrb[ii])
			 if(wstrb[ii]) 
				wdata[8*ii+:8] inside {valid_byte}; 
			} 
constraint valid_strobe { foreach(wstrb[ii])
				wstrb[ii] inside {0,1};
			}
constraint solver1 { solve wstrb before wdata;}
constraint solver2 { solve valid_byte before wstrb;}


endclass : abc 
```

#### Question3
```md
---
Q3: There are 4 strings RED, GREEN, BLUE, YELLOW and a sequence of numbers {0,1,2,3,4,5,6,7,8,9}. A card datatype contains both a string sequence and a number sequence which is a subset of the former.

Write SV code/constraint such that everytime you pick 3 cards, they get same string and a consecutive sequence of numbers as its' items
 
---
```

```cpp
//One possible solution(maybe)
class abc;

rand string string_key[];
rand bit[3:0] number_value[];

constraint number_value_init { 
			     number_value.size() == 3;
				
			     foreach(number_value[ii])
				number_value[ii] == ii; //consecutive
			     
			     foreach(number_value[ii])
				number_value[ii] inside {[0:9]};
			     }

constraint string_key_init   {
			      string_key.size() == 3;
			      
			      foreach(string_key[ii])
				foreach(string_key[jj])
				 if(ii!=jj)
				    string_key[ii] == string_key[jj];//all elements same
                              
			      foreach(string_key[ii])
				 string_key[ii] inside {"RED", "GREEN", "BLUE", "YELLOW"};
			     }

constraint solver {solve string_key before number_value;}
				 
//create a card datatype --> union is close

typedef struct packed
{
string_key;
number_value;
}
card_t;

rand card_t card[]; //take an array of cards


 
endclass: abc 
```



#### Question4
```md
---
Q4: Suppose you are writing a TB for a memory model which has the following signals
input wr_en = write_enable
input rd_en = read_enable
input addr = address
input wdata = write data
input cs = chip select
input valid = valid transaction on input side
input wstrb = indicating which are valid byte lanes in wdata
output rdata = read data

Write the basic code (just the scratch template) for the sequence item and possible driving logic (write + read)
and sampling function/logic for wdata on basis of wstrb which can be used in monitor
---
```
```cpp
//Definitions
`ifndef vip_def
`define vip_def

`define ADDR_WIDTH = 4
`define DATA_WIDTH = 32 
`endif
```
```cpp
//Sequence item

class mem_seq_item extends uvm_sequence_item;

`uvm_object_utils(mem_seq_item)

rand bit [`ADDR_WIDTH-1:0] addr; 
rand bit [`DATA_WIDTH-1:0] wdata;
rand bit wr_en;
rand bit rd_en;
rand bit [`DATA_WIDTH/8 - 1:0] wstrb; //max width = number byte lanes in data bus
bit [`DATA_WIDTH-1:0] rdata;

//constructor
function new(string name = "mem_seq_item");
super.new(name);
endfunction

//constraints
//wr_en and rd_en should be mutually exclusive

constraint wr_rd_exc {wr_en != rd_en; }

//wstrb bits should be either 0 or 1

constraint wstrb_valid { foreach (wstrb[ii]) wstrb[ii] inside {0,1}; }

endclass : mem_seq_item
```


```cpp
//driver
class mem_driver extends uvm_driver#(mem_seq_item);

`uvm_component_utils(mem_driver) //registration

virtual mem_if vif; //virtual intf local handle

//constructor
function new(string name, uvm_component parent);
super.new(name, parent);
endfunction:new

//build phase
//code template + get vif
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);

 if(!uvm_config_db#(virtual mem_if) :: get(this, "", "vif", vif))
	`uvm_error("mem_driver", "failed to get vif for mem_driver")
endfunction : build_phase

//run_phase
virtual task run_phase(uvm_phase phase);

forever begin
seq_item_port.get_next_item(req); //req is an in built handle for seq item mem_seq_item
drive(req);
seq_item_port.item_done(); 
end
endtask : run_phase

virtual task drive(req);
vif.wr_en <= 0;
vif.rd_en <= 0;
vif.valid <= 0;
vif.wstrb <= 0;
vif.cs <= 1; //select the chip
@(posedge vif.clk);
vif.addr <= req.addr; //give the addr

if(req.wr_en)begin
vif.wr_en <= req.wr_en;
vif.wstrb <= req.wstrb;
vif.wdata <= req.wdata;
@(posedge vif.clk); //wait 1 more clock
end

if(req.rd_en)begin
vif.rd_en <= req.rd_en;
@(posedge vif.clk); //wait 1 clock to make rd_en 0
vif.rd_en <= 0;
@(posedge vif.clk);//Wait 1 more to get read data
req.rdata <= vif.rdata;
end
endtask : drive

endclass : mem_driver

```
```cpp
//function for sampling wdata on basis of wstrb in monitor
function logic[`DATA_WIDTH-1:0] sample_data_on_strb
(
	input bit [`DATA_WIDTH-1:0] wdata, 
	input bit [`DATA_WIDTH/8-1:0] wstrb
);

logic [`DATA_WIDTH-1:0] sampled_data; 

for (int i=0, j=0; i<`DATA_WIDTH/8; i++)
if(wstrb === 1'b1)begin
sampled_data[8*j+:8] = wdata[8*i+:8];
j++;
end

return sampled_data;

endfunction : sample_data_on_strb


//Ex- wdata[31:0] = abcdef9a (hex)
//    wstrb[3:0] = 1100 (binary)

//i = 0, wstrb[0]=0, skip
//i = 1, wstrb[1]=0, skip
//i = 2, wstrb[2]=1, wdata[8*2:8*2+8-1] = sampled_data[8*0:8*0+8-1] = cd (hex), j=1
//i = 3, wstrb[3]=1, wdata[8*3:8*3+8-1] = sampled_data[8*1:8*1+8-1] = ab (hex), j=2  
```
#### Question5
```md
---
Q5: Explain the concept of polymorphism by code
```
```cpp
class parent;
 virtual function void print();
 $display("this is parent");
 endfunction
endclass:parent

class child extends parent;
function void print();
$display("this is child");
endfunction
endclass

module poly;
intial begin
//case 1
begin
parent p;
child c;
p = new;
c = new;

p.print(); //Ans - "this is parent"
c.print(); //Ans - "this is child"
//In this case different forms of the method print(of parent class) is done by naming the parent method as virtual
//So basically when we call the child print method it first determines the type of handle the child has.
//Now child class is pointing to no one else and is of type child and so it goes up the hierarchy and finds that the called function type to be 
//virtual in parent. So it comes down and calls child implementation 
end

//case 2
begin
parent p;
child c;
c = new;
p = c; //This is legal child instance can be copied to parent since it contains subclass of type child only

p.print(); //Ans - "this is child"
c.print(); //Ans - "this is child"

//When we call parent print method it looks for the handle type it is containing. It is containing c/child type handle.
//so child function is called
//When we call child print method it does the same as case 1
end

//case3
begin
parent p;
child c;
/*
p = new;
c = p;
Above block is illegal you cannot assign parent to child because child does not contain a subclass of type parent! 
*/

//So we need dynamic casting as below


child c_temp;

c = new; //create child instance
p = c; //parent now contains child
//c_temp = p; //Static casting or copying will fail due to static type checking at compile time 
$cast(c_temp, p); //Dynamic casting will be a success due to dynamic type checking at run time

p.print();//Ans- "this is child"
c_temp.print();//Ans - "this is child"
//Now p is pointing to child. So child function will be called because of virtual method
//c_temp is pointing to parent which in turn points to child, so child function will be called because of virtual method
end


end
endmodule
```
#### Stretch Question on above
```md
---
Q5.1: If you declare the child method as also virtual what will happen
```
```
Ans - Child methods are by default virtual even if they are not explicitly mentioned/declared provided the parent's method is virtual

So for all the cases i.e., 1,2,3 prints will remain the same
```
#### Stretch Question on above
```md
---
Q5.2: If you don't put virtual keyword in both child and parent what will happen
```
```
Now methods will be called solely depending on class type 
If function/method names are same in parent and child, child method will override parent method
And even if a parent class is pointing to child instance 
or a child handle is pointing to parent which in turn is pointing to child instance....none of that matters
because when you will call the methods it will be called solely on class types i.e., 
visibility of methods is limited to the type of class it is and not on the type of handle it is pointing to

So 
For case 1,2,3:
print1 - "this is parent"
print2 - "this is child"
```

#### Question6
```md
---
Q6: Suppose you are given to code AXI master agent which will send aligned address in AWADDR. Code the basic sequence item and constraint 
needed for it which will be simulator/emulator friendly   
```
```cpp
class axi_sequence_item extends uvm_sequence_item;

....//all the necessary stuffs
rand logic [`AXI_ADDRESS_WIDTH -1 :0] AWADDR;
//burst_size will indicate how many bytes of data bus are used in each tranfers/beats(clk) according to AXI spec
typedef enum logic[2:0] //because AxSIZE[2:0]
{
1BYTE = 3'b000,
2BYTE = 3'b001,
4BYTE = 3'b010,
8BYTE = 3'b011,
16BYTE = 3'b100,
32BYTE = 3'b101,
64BYTE = 3'b110,
128BYTE = 3'b111 
}
burst_size;

rand burst_size burst_size_t;

constraint generate_burst_aligned_address{
	burst_size_t === 1BYTE -> AWADDR = AWADDR;//2**0 = 1
	burst_size_t === 2BYTE -> AWADDR[0] = 1'b0;//2**1 = 2 
	burst_size_t === 4BYTE -> AWADDR[1:0] = 2'b0;//2**2 = 4
	burst_size_t === 8BYTE -> AWADDR[2:0] = 3'b0;//2**3 = 8
	burst_size_t === 16BYTE -> AWADDR[3:0] = 4'b0;//2**4 = 16
	burst_size_t === 32BYTE -> AWADDR[4:0] = 5'b0;//2**5 = 32
	burst_size_t === 64BYTE -> AWADDR[5:0] = 6'b0;//2**6 = 64
	burst_size_t === 128BYTE -> AWADDR[6:0] = 7'b0;//2**7 = 128
};

constraint solver1 {solve burst_size_t before AWADDR};

....
endclass
```
#### Question7(High level)
```md
---
Q7: Suppose your AXI master is not sending burst aligned addresses for transfers. Provided you are given Burst zise and address how will you determine how many bytes it is unaligned to burst size   
```
```cpp

package abc;

//burst_size will indicate how many bytes of data bus are used in each tranfers/beats(clk)

enum logic[2:0] //because AxSIZE[2:0]
{
1BYTE = 3'b000,
2BYTE = 3'b001,
4BYTE = 3'b010,
8BYTE = 3'b011,
16BYTE = 3'b100,
32BYTE = 3'b101,
64BYTE = 3'b110,
128BYTE = 3'b111 
}
burst_size;

function byte calculate_unaligned_offset(
input bit[AXI_ADDR_WIDTH] address,
input bit[2:0] burst_size);

byte unaligned_offset;

case(burst_size)
1BYTE : unaligned_offset = 0;
2BYTE : unaligned_offest = byte'(address[0]); //Static cast to byte size 
//i.e., take the axsize no of bits in lsb and fill remaining msbs to 0s
4BYTE : unaligned_offset = byte'(address[1:0]);
8BYTE : unaligned_offset = byte'(address[2:0]);
16BYTE :unaligned_offset = byte'(address[3:0]);
....
endcase
return unaligned_offset;
endfunction : unaligned_offset
endpackage

```


