---
title: "OOP"
category: "General"
date: "2021-05-04 12:00:00 +09:00"
desc: "OOP Questions"
thumbnail: "./images/oop/download.png"
alt: "markdown logo"
---

```
Q1) Difference between overriding and overloading
```
```
Overloading - Function overloading is a feature that allows us to have same function more than once in a program. Overloaded functions have same name but their signature must be different

System verilog does not support overloading

Method Overloading is a Compile time polymorphism. In method overloading, more than one method shares the same method name with different signature in the class. In method overloading, return type may or may not be the same, but we must have to change the parameter because in java, we can not achieve the method overloading by changing only the return type of the method
```

```cpp

///Below piece of code is illegal in case of system verilog where same function with same names with different signatures are present multiple times inside a class
class MethodOverloadingEx;

function int add(input int a, b);
add = a + b;
endfunction: add

function int add(input int a, b, c);
add = a + b + c;
endfunction: add

endclass: MethodOverloadingEx 
```

```java

///Below piece of code is legal in java where same function with same names with different signatures(input parameter list) are present multiple times inside a class
class MethodOverloadingEx{  
   static int add(int a, int b){return a+b;}  
   static int add(int a, int b, int c){return a+b+c;}  
 
    public static void main(String args[]) {
      System.out.println(add(4, 6));
      System.out.println(add(4, 6, 7));
    }
} 
```
```
Function overriding is a feature of OOPs Programming that allows us to override a function of parent class in child class

This feature is available in system verilog and C++ and Java

Method Overriding is a Run time polymorphism. In method overriding, derived class provides the specific implementation of the method that is already provided by the base class or parent class. In method overriding, return type must be same or co-variant (return type may vary in same direction as the derived class).
```
```cpp
// Below is the example of overriding where base class "eat" function is overrided in child class implementation. Function name and signature must be same in both for this to occur

class animal;

function void eat();
$display("eating.");
endfunction : eat

endclass : animal

class dog extends animal;

function void eat();
$display("Dog is eating.");
endfunction : eat

endclass : dog

class MethodOverridingEx;

dog d1;
animal a1;

function void override();
d1 = new();
a1 = new();
d1.eat(); //will print "Dog is eating."
a1.eat(); //will print "eating."
endfunction : override


endclass : MethodOverridingEx

```

```java
// Below is the example of overriding where base class "eat" function is overrided in child class implementation. Function name and signature must be same in both for this to occur

class animal{  
      void eat(){System.out.println("eating.");}  
      }  
    class dog extends animal{  
    void eat(){System.out.println("Dog is eating.");}  
     }  
   class MethodOverridingEx{  
    public static void main(String args[]) {
      dog d1=new dog();
      animal a1=new animal();
      d1.eat(); //will print "Dog is eating."
      a1.eat(); //will print "eating."
    }
} 

```

| Method Overloading                                              | Method Overriding                                                             |
|-----------------------------------------------------------------|:-----------------------------------------------------------------------------:|
| compile time polymorphism                                       |run time polymorphism                                                          |
| methods must have same name and different signature             |methods must have same name and same signature                                 |
| return type can or can not be be same                           |return type must be same or co-variant                                         |
| may or may not require inheritance                              |always needs inheritance                                                       |
| within single class                                             |in two classes with inheritance relationship                                   |
| help to rise the readability of the program                     |it is used to grant the specific implementation in child class of parent method|
