---
title: "UVM Basics"
category: "Code"
date: "2020-01-28 12:00:00 +09:00"
desc: "Data Modelling (under 🚧!)"
thumbnail: "./images/code-block/thumbnail.jpg"
alt: "code block graphic"
---

## Objective

In this post we will 
* Model the data transaction items for the inputs and outputs of the DUT
* Define default constraints and switches to control randomization
* Add the necessary constructs to use data items in a UVM environment
* Add UVM automation using the UVM "opt-in" system to allow printing, copying and comparing

## Requirement

What we are going to do 
* Model basic building blocks for data representation - e.g., packets, CPU transactions, register operations

What do we need 
* Generation of data through randomization or direct specfication - With default random behavior creating legal data
* Sequence-level control - If the first 5 packets don't have errors, then inject three parity errors in succession
* Abstraction from protocol details - Signal-level details of sending a packet are modeled in the driver layer
* Data visualization through automation - Printing both control and physical fields

Let's go! 👍

## Data Item example: YAPP Packet

```cpp
class yapp_packet;
  rand bit [5:0] length; //-->rand needs to be randomized
  rand bit [1:0] addr;   //-->rand needs to be randomized
  rand bit [7:0] payload[]; //-->rand needs to be randomized
                            //-->payload is a dynamic array
                            //-->size and contents are randomized so needs constraint on size!
       bit [7:0] parity; //--> parity is not rand since parity is calculated on payload + header
  // control fields
  rand int packet_delay; //-->Clock cycle delay b/w packets

  // utility functions
  function bit [7:0] calc_parity (); //-->parity is calculated using this method
  ...

  function void post_randomize (); //--> packet_handle.randomize() method calls post_randomize()
                                   //--> update parity in post_randomize()
    // update parity
  ...
endclass: yapp_packet
```
But we also need control over generation of good and bad parity packets

Let's do this 👇

## Use knobs
```cpp
typedef enum bit {BAD_PARITY, GOOD_PARITY} parity_t;
//-->knobs are control fields that allow easy user interface
class yapp_packet;
  rand bit [5:0] length;
  rand bit [1:0] addr;
  rand bit [7:0] payload[];
       bit [7:0] parity;
  
  // control fields
  rand int packet_delay;
  rand parity_t parity_type; 
  //-->test writers can specify the distribution of good vs. bad parity

  function bit [7:0] calc_parity(); 
  //-->calculates correct parity
  ...

  function void set_parity();
    parity = calc_parity();
    if (parity_type == BAD_PARITY)
    //--> sets parity based on the parity type knob
      parity = ~parity;
  ...

  function void post_randomize();
    set_parity();
    //-->parity updated in post_randomize()
  ...
endclass: yapp_packet
```
## Some basic constraints
```cpp
typedef enum bit {BAD_PARITY, GOOD_PARITY} parity_t;
class yapp_packet;
  rand bit [5:0] length;
  rand bit [1:0] addr;
  rand bit [7:0] payload[];
       bit [7:0] parity;
  
  //--> control fields
  rand int packet_delay;
  rand parity_t parity_type;

  //-->default constraints
  constraint payload_size     {   length == payload.size();   }
  //-->dependency constraint to make length = size of payload array
  constraint default_length   {   length > 0; length < 64;    }
  //-->0 payload is illegal so to make it legal 
  constraint medium_pkt_delay {   packet_delay > 1; packet_delay < 20;  }
  //-->intra-packet delays cannot be -ve and also cannot a very huge value

  //utility functions
  ...
endclass: yapp_packet
```
## Add methods for parity calculation and class construction
```cpp
//------------------------------------------------------------------------------
//
// yapp packet enums, parameters, and events
//
//------------------------------------------------------------------------------
typedef enum bit { BAD_PARITY, GOOD_PARITY } parity_t;
 
//------------------------------------------------------------------------------
//
// CLASS: yapp_packet
//
//------------------------------------------------------------------------------

class yapp_packet extends uvm_sequence_item;     

  // Physical Data
  rand bit [5:0]  length;
  rand bit [1:0]  addr;
  rand bit [7:0]  payload [];
  bit      [7:0]  parity;      // calculated in post_randomize()

  // Control Knobs
  rand parity_t parity_type;
  rand int packet_delay;

  // UVM macros for built-in automation - These declarations enable automation
  // of the data_item fields 
  `uvm_object_utils_begin(yapp_packet)
    `uvm_field_int(length,       UVM_ALL_ON)
    `uvm_field_int(addr,         UVM_ALL_ON)
    `uvm_field_array_int(payload, UVM_ALL_ON)
    `uvm_field_int(parity,      UVM_ALL_ON)
    `uvm_field_enum(parity_t, parity_type, UVM_ALL_ON)
    `uvm_field_int(packet_delay, UVM_ALL_ON | UVM_DEC | UVM_NOCOMPARE)
  `uvm_object_utils_end

  // Constructor - required syntax for UVM automation and utilities
  function new (string name = "yapp_packet");
    super.new(name);
  endfunction : new

  // Default Constraints
  constraint default_length { length > 0; length < 64; }
  constraint payload_size   { length == payload.size(); }
  constraint default_delay  { packet_delay >= 0; packet_delay < 20; }

  // Constrain for mostly GOOD_PARITY packets
  constraint default_parity { parity_type dist {BAD_PARITY := 1, GOOD_PARITY := 5}; }
  // Constraint address - Only 0, 1, 2 are valid addresses
  constraint default_addr  { addr != 2'b11; }
 
  // Calculates correct parity over the header and payload
  function bit [7:0] calc_parity();
    calc_parity = {length, addr};
    for (int i=0; i<length; i++)
      calc_parity = calc_parity ^ payload[i];
  endfunction : calc_parity

  // sets parity field according to parity_type
  function void set_parity();
    parity = calc_parity();
    if (parity_type == BAD_PARITY)
      parity++;
  endfunction : set_parity

  // post_randomize() - sets parity
  function void post_randomize();
    set_parity();
  endfunction : post_randomize

endclass : yapp_packet
```
