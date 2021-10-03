---
title: "Force Files"
category: "GLS"
date: "2020-10-03 12:00:00 +09:00"
desc: "Some basic commands of forces used in GLS"
thumbnail: "./images/GLS/GLS.png"
alt: "markdown logo"
---

##  Force Files

```md
Force files are used for forcing **non resettable** flops. 
Sometimes netlist has issues where some signals are not driven as expected. 
To temporarily fix this, we use force on that signal to get the required behaviour. 
Towards the end of project these forces need to be removed.
```


#### Example

```md
- force -freeze takes effect till end of simulation or until force -release is called.
- **force -deposit** will only take effect till some other driver drives the signal. When some other driver drives the signal new value will be reflected.
- If synthesis happened properly and non-resettable flops are initialized properly, force deposit would not be required. 
```

