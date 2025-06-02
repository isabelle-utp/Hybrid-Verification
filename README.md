# Hybrid-Verification

This repository contains the Isabelle Verification with Ordinary Differential Equations (IsaVODEs) tool. It is a tool for verifying hybrid systems in Isabelle/HOL, and is a collaboration between [Jonathan Julián Huerta y Munive](http://orcid.org/0000-0003-3279-3685), [Simon Foster](https://orcid.org/0000-0002-9889-9514) and others. The tool provides an implementation of various techniques for reasoning about hybrid programs and differential equations, including André Platzer's [differential induction technique](http://www.ls.cs.cmu.edu/KeYmaeraX/), and also the use of flows and solutions.

In order to use this tool, you currently need Isabelle2025, the [Ordinary Differential Equations AFP entry](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html), and a set of components from our other repositories. The dependencies you need include:
* [Optics](https://github.com/isabelle-utp/Optics), `main` branch
* [Shallow Expressions](https://github.com/isabelle-utp/Shallow-Expressions), `main` branch
* [Hybrid Library](https://github.com/isabelle-utp/Hybrid-Library), `main` branch
* [Z_Toolkit](https://github.com/isabelle-utp/Z_Toolkit), `main` branch
* [CAS-Integration](https://github.com/isabelle-utp/CAS-Integration), `master` branch

Make Isabelle aware of them either by editing your ``ROOTS`` file (in `/Users/user_name/.isabelle/Isabelle2025/ROOTS`), or by making them [Isabelle components](https://www.isa-afp.org/help/). Users may start Isabelle with the Hybrid-Verification heap image already built-in with ``isabelle jedit -R Framed_ODEs`` to make the start time quicker. Once done, you should be able to run the theories in this repository.

#### Papers describing this work:
* Certifying Differential Equation Solutions from Computer Algebra Systems in Isabelle/HOL. In ArXiV 2021: [https://arxiv.org/abs/2102.02679](https://arxiv.org/abs/2102.02679)
* Hybrid systems verification with Isabelle/HOL: Simpler syntax, better models, faster proofs. In FM 2021: [https://doi.org/10.1007/978-3-030-90870-6_20](https://doi.org/10.1007/978-3-030-90870-6_20)
* Affine systems of ODEs in Isabelle/HOL for hybrid-program verification. In SEFM 2020: [https://doi.org/10.1007/978-3-030-58768-0_5](https://doi.org/10.1007/978-3-030-58768-0_5)
* Differential Hoare logics and refinement calculi for hybrid systems with Isabelle/HOL. In RAMiCS 2020: [https://doi.org/10.1007/978-3-030-43520-2_11](https://doi.org/10.1007/978-3-030-58768-0_5)
* Predicate transformer semantics for hybrid systems. In JAR, 2022: [https://doi.org/10.1007/s10817-021-09607-x](https://doi.org/10.1007/978-3-030-58768-0_5)
