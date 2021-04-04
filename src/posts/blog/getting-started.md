---
title: "System Verilog questions"
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
s = new(0); //initially with 0 keys
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
s.get(2); //when you get 2 keys end execution by disabling threads
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

Constraint is when a valid byte is present in wdata, it has to be either 8'b11111111 or 8'b10101010
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

Write the basic code (just the scratch template) for the sequence item and possible driving logic (write + read) and also the sampling function/logic for wdata on basis of wstrb which can be used in monitor
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
Ans - Child methods are by default virtual even if they are not explicitly mentioned/declared, provided the parent's method is virtual

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
visibility of methods is limited to the type of class it is, and not on the type of handle it is pointing to

So 
For case 1,2,3:
print1 - "this is parent"
print2 - "this is child"
```

#### Question6
```md
---
Q6: Suppose you are given to code AXI master agent which will send aligned address in AWADDR according to AXI spec. Code the basic sequence item and constraint needed for it which will be simulator/emulator friendly   
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
}

constraint solver1 {solve burst_size_t before AWADDR};

....
endclass
```
```
You can solve the above by using modulo or (%) operator but when synthesized for running in emulation platform it will have more hardware cost.
Also above method is beneficial in terms of software operation cost. 
```
#### Question7(High level)
```md
---
Q7: Suppose your AXI master is not sending burst aligned addresses for transfers. Provided you are given Burst size and address, how will you determine how many bytes it is unaligned to burst size.   
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
```
You can solve the above by using modulo or (%) operator but when synthesized for running in emulation platform it will have more hardware cost.
Also above method is beneficial in terms of software operation cost. 
```
#### Question8
```md
---
Q8: Which datatype in SV will you use while modelling a big (say.,512MB) RAM   
```
```
When the size of the collection is unknown or the data space is sparse, 
an associative array is used, which does not have any storage allocated 
until it is used. That means, it is dynamically allocated, but has non-contiguous elements. 
Associative array’s index expression is not restricted to integral expressions, but can be of any type.

In RAM ,huge amount of data needs to be accessed , it's inefficient to declare the size in compile time,
because many spaces may left unused, so it is good to declare as associative array
```
#### Question9
```md
---
Q9: Which SV datatype does uvm_config_db uses to implement it's internal configuration database support 
and type overriding of elements at runtime
```
```
To build uvm_config_db we likely need a <key,value> pair lookup table which is accessible from anywhere and with any index type.
It should also have static "set" and "get" methods. So let us use associative array datatype for implementing the same.
"class_name :: set" & "class_name :: get" methods are used to store and retrieve information from database repectively.
```
```cpp
//Rough implementation
class uvm_config_db #(type T = int); //Type is dynamic, default type is integer

//declare a static assoc-array
static T db[string]; //return type of assoc-array is dynamic, default is int type
//Why static, because change of assoc-array by one method call will be visible to all 

//define static "set" method
static function void set(input string name, input T value); //set method takes the string index
//and value to be stored in assoc-array(config_db) in that index
db[name] = value;
endfunction : set

//define static "get" method
static function void get(input string name, ref T value); //get method takes the string index 
//and value to be obtained from assoc-array(config_db) from that index. value will be obtained as a reference/pointer
value = db[name];
endfunction : get

//define utility print function
static function void print();
$display("config_db%s", $typename(T)); //print the type of return type of config_db

foreach(db[i])
$display("db[%s]=%p", i, db[i]); //print key, value

endfunction : print

endclass : uvm_config_db

```
```cpp
//Let's use above config class

class test;
int i,j;
endclass : test
//
module abc;
int i=2;
int val;
real pi=3.14

//take handle of test class

test test_inst;

initial begin
//call set method
uvm_config_db#(int) :: set("i", i); 
//Above will create following entry within config_db class
//db["i"] =  2;

uvm_config_db#(real) :: set("pi", pi);
//Above will create following entry within config_db class
//db["pi"] =  3.14;

//take the instance of test class
test_inst = new();

test_inst.i = 8; //i=8 in test class instance
test_inst.j = 6; //j=6 in test class instance

uvm_config_db#(test) :: set("test_inst", test_inst);
//Above will create following entry within config_db class
//db["test_inst"] =  test_inst; // or pointer to test_inst

uvm_config_db#(int) :: get("i", val);
//Above will get the following entry value from within config_db class and return to user
//val = db["i"] = 2;

$display("get value of i from db is %0d", val); //will display 2

uvm_config_db#(int) :: print();
//Will print following display
//config_dbint
//db[i] = 2

uvm_config_db#(real) :: print();
//Will print following display
//config_dbreal
//db[pi] = 3.14

uvm_config_db#(test) :: print();
//Will print following display
//config_dbtest
//db[test_inst] = test_inst
end
```
```cpp
//Actual call to set and get methods in uvm are of the following format
//set from topmost component
string global_value = "soham";
uvm_config_db #(string) :: set(null, "uvm_test_top.*", "string_key", global_value); 
//Return 1- success or 0-failure
//get in sub components
string local_value;
uvm_config_db #(string) :: get(this, "", "string_key", local_value); 
```
#### Question10
```md
Q10: What is the need for a virtual interface in System verilog?
---
```
```md
* System verilog interface is static in nature, wheras classes are dynamic in nature. Because of this reason, it is not allowed to declare the interface within classes but it is allowed to refer to or point to the interface.
* A virtual interface is a variable of an interface type that is used in classes to provide access to physical interface signals.
* Classes are dynamic and so created at run time, while interfaces are static which is created at compile time. So if you instantiate a physical interface within a class, it will throw compilation error while compliation.   
```
#### Question11
```md
Q11: Write a SV constraint to generate unique elements in an array (very popular but quite old question)
```

```cpp
//Method 1
class abc;

rand bit[`DATA_WIDTH-1:0] data[];

constraint unique_array_constraint 
{ foreach(data[i])
  foreach(data[j])
  if(i!==j) 
  data[i]!=data[j];
}

endclass:abc

```
```cpp
//Method 2
class abc;

rand bit[`DATA_WIDTH-1:0] data[];

constraint unique_array_constraint
{
	unique {data};
}

endclass:abc
```
```cpp
//Method 3 - Though it is a solution it generates pseudo-random elements., i.e., 
//predicatble to a certain extent. It is not true random
class abc;

rand bit[`DATA_WIDTH-1:0] data[];

constraint unique_array_constraint
{
	foreach(data[i])
	data[i] = i; //or i*i
}

function post_randomize();
	data.shuffle();
endfunction : post_randomize

endclass:abc
```

#### Question11
```md
Q11: What can be basic verification scenarios for a NOC with 2 masters accessing 4 slaves. The NOC can handle single protocol.
---
```

```md
* A bare minimum interconnect VIP should have master active/passive agents connected to the interface and slave IP components as DUT of different bus protocols. The active agents will drive transactions and passive agents will throw any error associated with protocol/timing 
* It should have a common interconnect/NOC scoreboard and a coverage monitor
* It should be able to handle multiple protocols
* It should be able to handle setting different transaction attributes(like cacheable, bufferable, prot, priority etc.,) on each channel
* It should be able to handle reconfigurable address mapping and routing on the fly by use of sempahores
* It should have proper response code checking for
	- Unmapped addresses
	- Unsecured accesses to secured memories
	- Transactions to a closed path (for power off or other reasons)
	- Custom policy
* It should be able to handle cache coherency
	- Communication between coherent masters - An additional coherency scoreboard can be developed comprising of masters which access shared data.
    This access should be properly communicated to all the concerned masters via coherency protocol and returned data must come from memory or cache
	- Proper passing of shared data between coherent masters
	- Accurate master ACE responses in regards to cache states
```

```md
**Probable testcases**
* Check single master accessing all slaves
* Check multiple master trying to get access of bus at same time. Master 1 of higher priority(say) should take hold of bus first and complete transaction. Immediately after it's completion, master 0 of lower priority(say) should finish it's transaction
* Master should access non-existent slaves with unmapped address and check bus signal behaviour
* Master should try to do both write and read in read only slave and check bus signal behaviour
* ...

```
#### Question12
```md
Q12: How to know which master has initiated transaction to or from which slave transaction is coming from, in case of a multimaster and multislave scenario
```

```md
As we know in AXI, ID field is associated with an atomic transaction. So from transaction only, we will not be able to decipher which master has issued it or which slaves' response is it. We can put a ID associated with each master & slave in User signal of AXI in transaction for this. 
```
```cpp

//master a monitor

class master_a_mon extends uvm_monitor;

transaction trans;

uvm_analysis_port#(transaction) ap1;

//new
ap1 = new("ap1", this);

//run_phase
trans = transaction::type_id::create("trans",this);
ap1.write(trans);

...
endclass: master_a_mon

/*-------------------------------------------------
---------------------------------------------------
-------------------------------------------------*/

//master b monitor
class master_b_mon extends uvm_monitor;

transaction trans;

uvm_analysis_port#(transaction) ap2;

//new
ap2 = new("ap2", this);

//run_phase
trans = transaction::type_id::create("trans",this);
ap2.write(trans);

...
endclass: master_b_mon
```
```cpp

//scoreboard
`uvm_analysis_imp_decl(_port_a)
`uvm_analysis_imp_decl(_port_b)

class scoreboard extends uvm_scoreboard;

uvm_analysis_imp_port_a #(transaction, scoreboard) imp_a;
uvm_analysis_imp_port_b #(transaction, scoreboard) imp_b;

//Queues for respective masters
transaction master_a[$];
transaction master_b[$];

int trans_cnt_mon_a;
int trans_cnt_mon_b;

//new
imp_a = new("imp_a", this);
imp_b = new("imp_b", this);

virtual function void write_port_a(transaction trans);
transaction sb_a;
$cast( sb_a, trans.clone() );
trans_cnt_mon_a++;

case(sb_a.user)
A:  begin
    	master_a.push_back[sb_a]; 
	end
B:  begin
    	master_b.push_back[sb_a];
    end
endcase
endfunction

virtual function void write_port_b(transaction trans);
transaction sb_b;
$cast( sb_b, trans.clone() );
trans_cnt_mon_b++;

case(sb_b.user)
A:	begin
		master_a.push_back(sb_b);
  	end
B:  begin
	    master_b.push_back(sb_b);
	end
endcase
endfunction

endclass : scoreboard
```

```cpp
//Environment
class environment extends uvm_env;
//instances

//connect phase
function void connect_phase(uvm_phase phase);

master_a_mon.ap1.connect(scoreboard.imp_a);
master_b_mon.ap2.connect(scoreboard.imp_b);

endfunction
...
endclass
```
```

```
#### Question13
```md
Q13: What is the difference between m_sequencer and p_sequencer 
```
```md
* m_sequencer is default sequencer and p_sequencer is typecast to m_sequencer
* m_sequencer is a handle of type uvm_sequencer_base which is available by default in a sequence
  - It is determined by the following-
    - the sequencer handle provided in the start method
	- the sequencer used by the parent sequence
    - the sequencer that was set using the set_sequencer method
* The real sequencer on which a sequence is running would normally be derived from the uvm_sequencer_base class. Hence to access the real sequencer on which sequence is running , you would need to typecast the m_sequencer to the physical sequencer which is generally called p_sequencer
* Since p_sequencer is a typed-specific sequencer pointer, it is generally created by registering the sequence to the sequencer using macro (`uvm_declare_p_sequencer). The p_sequencer is used to access the sequencer properties.
```
```cpp
//An example
//Let's say a sequence wants to access a component(monitor_a., say) which is available with its' sequencer

class sequencer_c extends uvm_sequencer;

	monitor_a monitor_a_inst1;
endclass : sequencer_c
```
```cpp
class sequence_c extends uvm_sequence

	sequencer_c p_sequencer;
	//or
	`uvm_declare_p_sequencer(sequencer_c)

	monitor_a monitor_a_inst2;

	task pre_body();

	//Typecast the m_sequencer base type to p_sequencer

	if( !$cast(p_sequencer, m_sequencer) ) 
	begin
		`uvm_error("sequence_c:","Sequencer type mismatch ... cast failed")
	end

	//Now you can access after typecasting

	monitor_a_inst2 = p_sequencer.monitor_a_inst1;

	endtask : pre_body

endclass: sequence_c
```
```
#### Question14
```md
Q14: What is the difference between virtual sequencer and a normal sequencer 
```
```
Virtual sequencer contains pointers to real physical sequencers where sequences can run upon. It is not bothered with data driving part. It does not communicate with real physical drivers. It's job is only to have the handles of child sequencers and point them to actual physical sequencers of agents respectively.
```
#### Stretch Question on above
```md
Q14: What is the use of virtual sequencer in your SoC Testbench 
```
```md
* It contains handles of the sequencers which are located in different agents
* If stimulus generation across different interfaces has to be synchronized, it is done by Virtual sequencer and virtual sequences
* In practical if you have two IPs in an SoC and you want to have stimulus control, virtual sequencer, virtual sequences helps to achieve it
```
```cpp
//Consider seqr1 and seqr2 are handles of seqrs which belongs to agents seq1_agent and seq2_agent respectively within environment "env"
class v_seqr extends uvm_sequencer;
`uvm_component_utils(v_seqr)

//Handles of seqrs
type1_seqr seqr1;
type2_seqr seqr2;

//constructor
function new(string name="v_seqr", uvm_component parent);
super.new(name,parent);
endfunction:new

endclass:v_seqr

```
```cpp
//Instantiate v_seqr within virtual sequence "virtual_base_seq"

class base_virtual_seq extends uvm_sequence#(uvm_sequence_item);

`uvm_object_utils(base_virtual_seq)

type1_seqr seqr1;
type2_seqr seqr2;

v_seqr v_seqr_inst;
//or you can use `uvm_declare_p_sequencer macro

//constructor
function new(string name="base_virtual_seq");
super.new(name);
endfunction:new

task body();
if(!$cast(v_seqr_inst, m_sequencer)) begin
`uvm_error(get_full_name(), "v_seqr pointer cast failed")
end
//After casting assign the null pointers to actual child sequencers 
this.seqr1 = v_seqr.seqr1;
this.seqr2 = v_seqr.seqr2;

endtask:body

endclass:base_virtual_seq
```
```cpp
//Let's define virtual sequence

class v_seq extends base_virtual_seq;
`uvm_object_utils(v_seq)

type1_seqr seqr1;
type2_seqr seqr2;
//virtual sequencer handle
v_seqr v_seqr_inst;

//constructor
function new(string name="v_seq");
super.new(name);
endfunction:new

task body();

//call parent body to assign sub_sequence handles correctly
super.body();

//take handles of actual sequences
//for time being, assume there are sequence classes of below names
type1_seq seq1;
type2_seq seq2;

//create seqs
seq1 = type1_seq::type_id::create("seq1");
seq2 = type2_seq::type_id::create("seq2");

//start the sequences
repeat(10)begin
seq1.start();
seq2.start();
end
endtask:body

endclass:v_seq
```
```cpp
//Environment will contain v_seqr, agents, and make connection of v_seqr to actual agent seqrs

...
function void connect_phase(uvm_phase phase);
v_seqr.seqr1 = seq1_agent.m_sequencer;
v_seqr.seqr2 = seq2_agent.m_sequencer;
endfunction:connect_phase
...
```
```cpp
//Test will contain v_seq and env
...
virtual task run_phase(uvm_phase phase);
//create v_seq
v_seq_inst = v_seq::type_id::create("v_seq");
phase.raise_objection(this);
//start v_seq on v_seqr
v_seq_inst.start(env.v_seqr_inst);
phase.drop_objection(this);

endtask:run_phase
...
```



