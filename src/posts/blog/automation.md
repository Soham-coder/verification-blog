---
title: "A python script to create makefile"
category: "DV Automation"
date: "2021-04-11 12:00:00 +09:00"
desc: "A Makefile Generator. This solution can be extended to other file generation as well e.x., testbench component generation"
thumbnail: "./images/automation/scoreboard.png"
alt: "markdown logo"
---

## A Makefile Generator


#### Scenario

```
 In certain cases, we need for auto-generation of stuffs, be it files of testbench or other scripts etc., to reduce time and increase efficiency
```

#### Problem Statement  

```

- Let's create a basic python script for generating a C/C++ based Makefile

```

#### Solution

```md
- We will create a configuration file to store certain configurations related to the compilation of filetypes (say C and C++)

- Configuration file can be created in (.ini) format which will be subsequently read by "configparser" module of python

- After that, we will create a string object leveraging the all powerful yet simple "+=" or concatenation operator, which can then be written to a file to generate our desired file
```

#### Implementation
```
The configparser module from Python's standard library defines functionality for reading and writing configuration files as used by Microsoft Windows OS. Such files usually have .INI extension in Windows OS and can be of any extension in Unix OS

The INI file consists of sections, each led by a [section] header. Between square brackets, we can put the section’s name. Section is followed by key/value entries separated by = or : character. It may include comments, prefixed by # or ; symbol
```

```ini
# A sample Configuration file named makegen.cfg


[c] # c compiler section
compiler = gcc # items within section
flags = -g -Wall 
installPath = ~/bin/

[cpp] # c++ compiler section
compiler = g++ # items within section
flags = -Wall 
installPath = ~/bin/

```

```md
- Now our script will be named as makegen.py which will take some input command line args as options
- When a script has some runtime options to it we generally have a -h or --help option which will print the runtime options the file can take and also their description
- For this we can make use of "optparse" module of python
```
```
- Our help message will be as follows:

Usage
Usage: makegen.py [ -bcdfihostvx ]

Options:
  --version             show program's version number and exit
  -h, --help            show this help message and exit
  -b BUILDDIR, --build-dir=BUILDDIR
                        set build directory for project to use. Default: .
  -c COMPILER, --compiler=COMPILER
                        set compiler to use. Default: gcc
  -d DIRECTORY, --directory=DIRECTORY
                        directory for makegen to create Makefile for. Default:
                        .
  -f FLAGS, --flags=FLAGS
                        flags for the compiler and typed within quotes
  -i INSTALLPATH, --install-dir=INSTALLPATH
                        directory for 'make install'. Default: /usr/local/bin
  -o OUTPUTFILE, --output-target=OUTPUTFILE
                        output file name from compiler. Default: a.out
  -s SRCDIR, --source-dir=SRCDIR
                        set source directory for project to use. Default: .
  -t FILETYPE, --file-type=FILETYPE
                        the file type of your source files (ex. c, cpp).
                        Default: c
  -v                    enable verbose output
  -x CONFIGFILE, --config-file=CONFIGFILE
                        path to makegen config file. Default: ~/makegen.cfg
```

```python

#!/usr/bin/env python3

###########################
#       makegen.py        #
###########################

#Import the needed modules
import os
from optparse import OptionParser
from configparser import ConfigParser 

## Global variables which will be taken as default and can be accessed within functions
VERSION = "0.0.1"
flags = ""
outputFile = ""
directory = ""
compiler = ""
installPath = ""
builddir = ""
srcdir = ""
configFile = ""
fileType = ""
verbose = False

# Writing every part of code as functions and classes increases reusability and scalability and will refactor the code block

def debugPrint(*args): # Function to enable verbose output
    if verbose:
        for a in args:
            print((a), end=' ')
        print("")

def parseCommandline(): # Function to parse cmdline options and print utility help message
    global flags, outputFile, directory, compiler, installPath, builddir, srcdir, configFile, verbose, fileType
    # Get commandline arguments
    parser = OptionParser(usage="Usage: makegen.py [ -bcdfihostvx ]", version="makegen Version " + VERSION)
    parser.add_option("-b", "--build-dir", dest="builddir", help="set build directory for project to use. Default: .", default=".")
    parser.add_option("-c", "--compiler", dest="compiler", help="set compiler to use. Default: is gcc", default="")
    parser.add_option("-d", "--directory", dest="directory", help="directory for makegen to create Makefile for. Default: .", default=".")
    parser.add_option("-f", "--flags", dest="flags", help="flags for the compiler and typed within quotes", default="")
    parser.add_option("-i", "--install-dir", dest="installPath", help="directory for 'make install'. Default: /usr/local/bin", default="/usr/local/bin")
    parser.add_option("-o", "--output-target", dest="outputFile", help="output file name from compiler. Default: a.out", default="a.out")
    parser.add_option("-s", "--source-dir", dest="srcdir", help="set source directory for project to use. Default: .", default=".")
    parser.add_option("-t", "--file-type", dest="fileType", help="the file type of your source files (ex. c, cpp). Default: c", default = "c")
    parser.add_option("-v", dest="verbose", help="enable verbose output", action="store_true")
    parser.add_option("-x", "--config-file", dest="configFile", help="path to makegen config file. Default: ~/makegen.cfg", default="~/makegen.cfg")

    (options, args) = parser.parse_args() #parse_args() function returns as a tuple
    
    # Store parsed arguments as variables
    outputFile = options.outputFile
    flags = options.flags
    directory = options.directory
    compiler = options.compiler
    installPath = options.installPath
    builddir = options.builddir
    srcdir = options.srcdir
    configFile = options.configFile
    verbose = options.verbose
    fileType = options.fileType

# Function to read the config file "makegen.cfg" through configparser module
# We store the items of each section in global variables "flags", "compiler", "installPath"

def parseConfig(fileType):
    global flags, compiler, installPath
    conf = ConfigParser()
    f = conf.read(os.path.expanduser(configFile))
    if len(f) == 0:
        debugPrint("Unable to find config file at " + configFile)
        return False
    debugPrint("Config file found at " + configFile)
    confFlags = confCompiler = confInstallDir = ""
    try:
      confFlags = conf.get(fileType, "flags")
    except:
        pass
    try:
        confCompiler = conf.get(fileType, "compiler")
    except:
        pass
    try:
        confInstallDir = conf.get(fileType, "installPath")
    except:
        pass
    if len(confFlags) != 0 :
        flags = confFlags
    if len(confCompiler) != 0:
        compiler = confCompiler
    if len(confInstallDir) != 0:
        installPath = confInstallDir
    return True

# Function to store compiler variable depending on "file-type" option passed
def setCompiler(fileType):
    global compiler
    if compiler != "":
        return
    if fileType in ["c", "s", "asm"]:
        compiler = "gcc"
    elif fileType in ["cc", "cpp", "cxx", "cp"]:
        compiler = "g++"
    else:
        print(("File type '" + fileType + "' not supported yet. Defaulting to gcc."))
        compiler = "gcc"


# Function to generate flags for the particular compiler
def flagsForCompiler(compilerName): # CompilerName will be obtained from the global compiler variable
    compilerVarName = ""
    compilerFlagsName = ""

    if compilerName == "g++":
        compilerVarName = "CXX"
        compilerFlagsName = "CXXFLAGS"
    else:
        # Default to gcc with C setup
        compilerVarName = "CC"
        compilerFlagsName = "CFLAGS"

    flagVars =  compilerVarName + " := " + compilerName + "\n"
    
    flagVars += compilerFlagsName + " := " + flags + "\n"
    ## Use MAKEGEN_COMPILER_FLAGS and MAKEGEN_COMPILER to keep it track of compiler and flags for internal use
    flagVars += "MAKEGEN_COMPILER := $(" + compilerVarName + ")\n"
    flagVars += "MAKEGEN_COMPILER_FLAGS := $(" + compilerFlagsName + ")\n"
    
    return flagVars


# Function to generate contents of the Makefile
def generateFileContents(fileType, compilerName):
    fileContents = "# Generated by makegen version " + VERSION + "\n# Makegen was written by Soham Mondal \n\n"

    # Compiler specific variables
    fileContents += flagsForCompiler(compilerName)
    fileContents += "SRCEXT := " + fileType + "\n"
    fileContents += "SRCDIR := " + srcdir + "\n"
    fileContents += "BUILDDIR := " + builddir + "\n"
    fileContents += "INSTALL_PATH := " + installPath + "\n"
    fileContents += "TARGET := " + outputFile + "\n"
    fileContents += "SOURCES := $(wildcard $(SRCDIR)/*.$(SRCEXT))\n"
    fileContents += "OBJECTS := $(patsubst $(SRCDIR)/%.o,$(BUILDDIR)/%.o,$(SOURCES:.$(SRCEXT)=.o))\n"

    fileContents += "\n\nall: $(TARGET)\n\n"

     # Main compilation
    fileContents += "$(TARGET): " + ("$(OBJECTS)\n")
    fileContents += "\t$(MAKEGEN_COMPILER) " + ("") + "-o $(TARGET) " + ("$^") + "\n\n"

    # Object files
    fileContents += "$(BUILDDIR)/%.o: $(SRCDIR)/%.$(SRCEXT)\n"
    fileContents +="\t$(MAKEGEN_COMPILER) $< $(MAKEGEN_COMPILER_FLAGS) -c -o $@\n"

    ## Clean
    fileContents += "\n"
    fileContents += "clean:" + "\n"
    fileContents += "\t" + "-rm $(TARGET) " + ("$(OBJECTS)") + "\n"

    ## Run
    fileContents += "\n"
    fileContents += "run: all\n"
    fileContents += "\t./$(TARGET)\n"

    ## Install
    fileContents += "\n"
    fileContents += "install: $(TARGET)\n"
    fileContents += "\tinstall $(TARGET) $(INSTALL_PATH)\n"

    ## Uninstall
    fileContents += "\n"
    fileContents += "uninstall:\n"
    fileContents += "\t-rm $(INSTALL_PATH)/$(TARGET)\n"


    return fileContents


# Write to Makefile the file contents
def writeToMakefile(fileContents):
    makefile = open("Makefile", 'w')
    makefile.write(fileContents)
    makefile.close()

# Main function calling all sub-functions in order
def start():
    parseCommandline()
    os.chdir(directory) # Change the directory to the directory that is passed in the options
    debugPrint("src directory ",srcdir)
    setCompiler(fileType)
    debugPrint("Compiler is set to " + compiler)

    parseConfig(fileType)

    fileContents = generateFileContents(fileType, compiler)
    writeToMakefile(fileContents)
    debugPrint("Successfully generated Makefile.")

    exit(0)


# Call the main function 
if __name__ == "__main__":
    start()
```

```
Sample run command:

First make the script executable (one time)
- chmod +x makegen.py

Then execute the script to generate Makefile
- makegen.py --build_dir="build" --compiler="g++" --directory="." --output-target="a.out" --source-dir="src" --file-type="cpp" -v --config-file="~/makegen.cfg"

```
```mk

# A sample makefile that will be created...


# Generated by makegen version 0.0.1
# Makegen was written by Soham Mondal

CXX := g++
CXXFLAGS := -Wall -g
MAKEGEN_COMPILER := $(CXX)
MAKEGEN_COMPILER_FLAGS := $(CXXFLAGS)
SRCEXT := cpp
SRCDIR := src
BUILDDIR := build
INSTALL_PATH := ~/bin/
TARGET := a.out
SOURCES := $(wildcard $(SRCDIR)/*.$(SRCEXT))
OBJECTS := $(patsubst $(SRCDIR)/%.o,$(BUILDDIR)/%.o,$(SOURCES:.$(SRCEXT)=.o))


all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(MAKEGEN_COMPILER) -o $(TARGET) $^

$(BUILDDIR)/%.o: $(SRCDIR)/%.$(SRCEXT)
	$(MAKEGEN_COMPILER) $< $(MAKEGEN_COMPILER_FLAGS) -c -o $@

clean:
	-rm $(TARGET) $(OBJECTS)

run: all
	./$(TARGET)

install: $(TARGET)
	install $(TARGET) $(INSTALL_PATH)

uninstall:
	-rm $(INSTALL_PATH)/$(TARGET)
```

```
So, as you can see it has created a Makefile with all the passed options and the remaining options args which were unspecified, were taken from the configuration file suitably !!

This Makefile can be treated as a sample generic makefile for compiling and installing C and C++ source files

The same concept can be applied for automatic generation of other files which deals with a one time solution or have monotonicity associated with them
```







