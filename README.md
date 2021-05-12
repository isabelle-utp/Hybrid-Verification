# Hybrid-Verification

This repository contains a set of components for verifying hybrid systems in Isabelle/HOL, and is a collaboration between Jonathan Julián Huerta y Munive, Simon Foster and others. The tool herein in provides an implementation of various techniques for reasoning about hybrid programs and differential equations, including Platzer's [differential induction technique](http://www.ls.cs.cmu.edu/KeYmaeraX/), and also the use of flows and solutions.

In order to use this tool, you currently need Isabelle 2020 (though we should upgrade to 2021 soon), and a set of components from our other repositories. The dependencies you need include:
* [Optics](https://github.com/isabelle-utp/Optics), branch isabelle2020
* [Shallow Expressions](https://github.com/isabelle-utp/Shallow-Expressions), branch main
* [Hybrid Library](https://github.com/isabelle-utp/Hybrid-Library), branch main

Check these out, and make Isabelle aware of them either by editing your ``ROOTS`` file, or by running ``isabelle jedit -d dirs``. Alternatively, it may be best to build the Hybrid Library heap image with ``isabelle build -b Hybrid-Library`` to make the start time quicker. Once done, you should be able to run the theories in this repository.
