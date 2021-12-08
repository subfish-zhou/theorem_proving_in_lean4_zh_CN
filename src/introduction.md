介绍
============

计算机和定理证明
-----------------------------

*形式验证*（Formal verification）包括使用逻辑和计算方法来验证用精确的数学术语表达的命题。这包括普通的数学定理，以及硬件或软件、网络协议、机械和混合系统中的形式命题。在实践中，验证数学命题和验证系统的正确性之间很类似：形式验证用数学术语描述硬件和软件系统，在此基础上验证其命题的正确性，这就像定理证明的过程。相反，一个数学定理的证明可能需要冗长的计算，在这种情况下，验证定理的真实性需要验证计算过程是否出错。

二十世纪的逻辑学发展表明，绝大多数传统证明方法可以简化为若干基础系统中的一小套公理和规则。有了这种简化，计算机能以两种方式帮助建立命题：它可以首先帮助寻找一个证明，并可以帮助验证一个所谓的证明是正确的。

*自动定理证明*（Automated theorem proving）着眼于 "寻找" 证明。解析定理证明器、表格法定理证明器、快速可满足性求解器等提供了在命题逻辑和一阶逻辑中验证公式有效性的方法。还有些系统为特定的语言和问题提供搜索和决策程序，例如整数或实数上的线性或非线性表达式。像SMT（satisfiability modulo theories）这样的架构将通用的搜索方法与特定领域的程序相结合。计算机代数系统和专门的数学软件包提供了进行数学计算或寻找数学对象的手段。计算也可以被看作是一种证明，而这些系统也可以帮助建立数学命题。

自动推理系统努力追求能力和效率，但往往牺牲稳定性。这样的系统可能会有bug，而且很难保证它们所提供的结果是正确的。相比之下，*交互式定理证明*侧重于 "验证" 证明，要求每个命题都有合适的公理基础的证明来支持。这就设定了非常高的标准：每一条推理规则和每一步计算都必须通过求助于先前的定义和定理来证明，一直到基本公理和规则。事实上，大多数这样的系统提供了精心设计的 "证明对象"，可以传给其他系统并独立检查。构建这样的证明通常需要用户更多的输入和交互，但它可以让你获得更深入、更复杂的证明。

*Lean 定理证明器*旨在融合交互式和自动化定理证明，它将自动化工具和方法置于一个支持用户交互和构建完整公理化证明的框架中。它的目标是支持数学推理和复杂系统的推理，并验证这两个领域的命题。

Lean的底层逻辑有一个计算的解释，与此同时Lean可以被视为一种编程语言。更重要的是，它可以被看作是一个编写具有精确语义的程序的系统，以及对程序所计算的功能进行推理。Lean也有机制作为它自己的*元编程语言*，这意味着你可以使用Lean本身实现自动化和扩展Lean的功能。Lean的这些方面将在本教程的配套教程【Lean 4编程】（*译者注：尚未完成*）中进行探讨，本书只介绍计算方面。

关于Lean
----------

*Lean* 项目由微软雷德蒙德研究院的Leonardo de Moura在2013年发起，这是个长期项目，自动化方法的潜力会在未来逐步被挖掘。Lean是在[Apache 2.0 license](LICENSE)下发布的，这是一个允许他人自由使用和扩展代码和数学库的许可性开源许可证。

通常有两种办法来运行Lean。第一个是网页版本：由Javascript编写，包含标准定义和定理库，编辑器会下载到你的浏览器上运行。这是个方便快捷的办法。

第二种是本地版本：本地版本远快于网页版本，并且非常灵活。Visual Studio Code和Emacs扩展模块给编写和调试证明提供了有力支撑，因此更适合正式使用。源代码和安装方法见[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/).

本教程介绍的是Lean的当前版本：Lean 4。

关于本书
---------------

本书的目的是教你在Lean中编写和验证证明，并且不太需要针对Lean的基础知识。首先，你将学习Lean所基于的逻辑系统，它是*依赖类型论*（dependent type theory）的一个版本，足以证明几乎所有传统的数学定理，并且有足够的表达能力自然地表示数学定理。更具体地说，Lean是基于具有归纳类型（inductive type）的构造演算（Calculus of Construction）系统的类型论版本。Lean不仅可以定义数学对象和表达依赖类型论的数学断言，而且还可以作为一种语言来编写证明。

由于完全深入细节的公理证明十分复杂，定理证明的难点在于让计算机尽可能多地填补证明细节。你将通过[依赖类型论](dependent_type_theory.md)语言来学习各种方法实现自动证明，例如项重写，以及Lean中的项和表达式的自动简化方法。同样，*阐释*（elaboration）和*类型推理*（type inference）的方法，可以用来支持灵活的代数推理。

最后，你会学到Lean的一些特性，包括与系统交流的语言，和Lean提供的对复杂理论和数据的管理机制。

在本书中你会见到类似下面这样的代码：

```lean
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
```

你可以在[Lean在线编辑器](https://leanprover-community.github.io/lean-web-editor/#)中尝试运行这些代码。（*译者注：该编辑器速度很慢，且目前只支持Lean 3，但足够运行本书中大多数代码。*）


致谢
---------------

This tutorial is an open access project maintained on Github. Many people have contributed to the effort, providing
corrections, suggestions, examples, and text. We are grateful to Ulrik Buchholz, Kevin Buzzard, Mario Carneiro, Nathan
Carter, Eduardo Cavazos, Amine Chaieb, Joe Corneli, William DeMeo, Marcus Klaas de Vries, Ben Dyer, Gabriel Ebner,
Anthony Hart, Simon Hudon, Sean Leather, Assia Mahboubi, Gihan Marasingha, Patrick Massot, Christopher John Mazey,
Sebastian Ullrich, Floris van Doorn, Daniel Velleman, Théo Zimmerman, Paul Chisholm, and Chris Lovett for their contributions.  Please see [lean prover](https://github.com/leanprover/) and [lean community](https://github.com/leanprover-community/) for an up to date list
of our amazing contributors.
