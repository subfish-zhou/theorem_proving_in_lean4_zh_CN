使用Lean进行工作
=====================

你现在已经熟悉了依赖类型论的基本原理，它既是一种定义数学对象的语言，也是一种构造证明的语言。现在你缺少一个定义新数据类型的机制。下一章介绍*归纳数据类型*的概念来帮你完成这个目标。但首先，在这一章中，我们从类型论的机制中抽身出来，探索与Lean交互的一些实用性问题。

并非所有的知识都能马上对你有用。可以略过这一节，然后在必要时再回到这一节以了解Lean的特性。

导入文件
---------------

Lean的前端的目标是解释用户的输入，构建形式化的表达式，并检查它们是否形式良好和类型正确。Lean还支持使用各种编辑器，这些编辑器提供持续的检查和反馈。更多信息可以在Lean[文档](http://leanprover.github.io/documentation/)上找到。

Lean的标准库中的定义和定理分布在多个文件中。用户也可能希望使用额外的库，或在多个文件中开发自己的项目。当Lean启动时，它会自动导入库中`Init'`文件夹的内容，其中包括一些基本定义和结构。因此，我们在这里介绍的大多数例子都是“开箱即用”的。

然而，如果你想使用其他文件，需要通过文件开头的`import'语句手动导入。命令

```
import Bar.Baz.Blah
```

导入文件``Bar/Baz/Blah.olean``，其中的描述是相对于Lean*搜索路径*解释的。关于如何确定搜索路径的信息可以在[文档](http://leanprover.github.io/documentation/)中找到。默认情况下，它包括标准库目录，以及（在某些情况下）用户的本地项目的根目录。你也可以指定相对于当前目录的导入；例如，导入是传递性的。换句话说，如果你导入了 ``Foo``，并且``Foo``导入了``Bar``，那么你也可以访问``Bar``的内容，而不需要明确导入它。

小节（续）
----------------

Lean提供了各种分段机制来帮助构造理论。你在[变量和小节](./dependent_type_theory.md#变量和小节)中看到，``section``命令不仅可以将理论中的元素组合在一起，还可以在必要时声明变量，作为定理和定义的参数插入。请记住，`variable`命令的意义在于声明变量，以便在定理中使用，如下面的例子：

```lean
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

``double``的定义不需要声明``x``作为参数；Lean检测到这种依赖关系并自动插入。同样，Lean检测到``x``在``t1``和``t2``中的出现，也会自动插入。注意，double*没有*``y``作为参数。变量只包括在实际使用的声明中。

命名空间（续）
------------------

在Lean中，标识符是由层次化的*名称*给出的，如``Foo.Bar.baz``。我们在[命名空间](./dependent_type_theory.md#命名空间)一节中看到，Lean提供了处理分层名称的机制。命令``namespace foo``导致``foo``被添加到每个定义和定理的名称中，直到遇到``end foo``。命令``open foo``然后为以`foo`开头的定义和定理创建临时的*别名*。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar
```

下面的定义

```lean
def Foo.bar : Nat := 1
```

被看成一个宏；展开成

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

尽管定理和定义的名称必须是唯一的，但标识它们的别名却不是。当我们打开一个命名空间时，一个标识符可能是模糊的。Lean试图使用类型信息来消除上下文中的含义，但你总是可以通过给出全名来消除歧义。为此，字符串``_root_``是对空前缀的明确表述。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type
```

我们可以通过使用``protected``关键字来阻止创建较短的别名：

```lean
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar
```

这通常用于像`Nat.rec`和`Nat.recOn`这样的名称，以防止普通名称的重载。

``open``命令允许变量。命令

```lean
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3
```

仅对列出的标识符创建了别名。命令

```lean
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3
```

给``Nat``命名空间中*除去*被列出的标识符都创建了别名。命令

```lean
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
```

将`Nat.mul`更名为`times`，`Nat.add`更名为`plus`。

有时，将别名从一个命名空间导出到另一个命名空间，或者导出到上一层是很有用的。命令

```lean
export Nat (succ add sub)
```

在当前命名空间中为``succ``、``add``和``sub``创建别名，这样无论何时命名空间被打开，这些别名都可以使用。如果这个命令在名字空间之外使用，那么这些别名会被输出到上一层。

属性
----------

Lean的主要功能是把用户的输入翻译成形式化的表达式，由内核检查其正确性，然后存储在环境中供以后使用。但是有些命令对环境有其他的影响，或者给环境中的对象分配属性，定义符号，或者声明类型类的实例，如[类型类](./type_classes.md)一章所述。这些命令大多具有全局效应，也就是说，它们不仅在当前文件中保持有效，而且在任何导入它的文件中也保持有效。然而，这类命令通常支持``local``修饰符，这表明它们只在当前``section``或``namespace``关闭前或当前文件结束前有效。

在[简化](./tactics.md#简化)一节中，我们看到可以用`[simp]`属性来注释定理，这使它们可以被简化器使用。下面的例子定义了列表的前缀关系，证明了这种关系是自反的，并为该定理分配了`[simp]`属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

然后简化器通过将其改写为``True``来证明``isPrefix [1, 2, 3] [1, 2, 3]``。

你也可以在做出定义后的任何时候分配属性：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

在所有这些情况下，该属性在任何导入该声明的文件中仍然有效。添加``local``修饰符可以限制范围：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp
```

另一个例子，我们可以使用`instance`命令来给`isPrefix`关系分配符号`≤`。该命令将在[类型类](./type_classes.md)中解释，它的工作原理是给相关定义分配一个`[instance]`属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

这个分配也可以是局部的：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#   ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
```

在下面的[符号](#符号)一节中，我们将讨论Lean定义符号的机制，并看到它们也支持``local``修饰符。然而，在[设置选项](#设置选项)一节中，我们将讨论Lean设置选项的机制，它并*不*遵循这种模式：选项*只能*在局部设置，也就是说，它们的范围总是限制在当前小节或当前文件中。

隐参数（续）
--------------------------

在[隐参数](./dependent_type_theory.md#隐参数)一节中，我们看到，如果Lean将术语``t``的类型显示为``{x : α} → β x``，那么大括号表示``x``被标记为``t``的*隐参数*。这意味着每当你写``t``时，就会插入一个占位符，或者说“洞”，这样``t``就会被``@t _``取代。如果你不希望这种情况发生，你必须写``@t``来代替。

请注意，隐参数是急于插入的。假设我们定义一个函数``f (x : Nat) {y : Nat} (z : Nat)``。那么，当我们写表达式`f 7`时，没有进一步的参数，它会被解析为`f 7 _`。Lean提供了一个较弱的注释，``{{y : ℕ}}``，它指定了一个占位符只应在后一个显式参数之前添加。这个注释也可以写成``⦃y : Nat⦄``，其中的unicode括号输入方式为``\{{``和``\}}``。有了这个注释，表达式`f 7`将被解析为原样，而`f 7 3`将被解析为``f 7 _ 3``，就像使用强注释一样。

为了说明这种区别，请看下面的例子，它表明一个自反的欧几里得关系既是对称的又是传递的。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 @th2 _ _ (@th1 _ _ reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
```

这些结果被分解成几个小步骤。``th1``表明自反和欧氏的关系是对称的，``th2``表明对称和欧氏的关系是传递的。然后``th3``结合这两个结果。但是请注意，我们必须手动禁用`th1`、`th2`和`euclr`中的隐参数，否则会插入太多的隐参数。如果我们使用弱隐式参数，这个问题就会消失：

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r
```

还有第三种隐式参数，用方括号表示，``[``和````]``。这些是用于类型类的，在[Chapter Type Classes](./type_classes.md)中解释。

符号
------------

Lean中的标识符可以包括任何字母数字字符，包括希腊字母（除了∀、Σ和λ，正如我们已经看到的，它们在依赖类型理论中有特殊的含义）。它们还可以包括下标，可以通过输入``\_``，然后再输入所需的下标字符。

Lean的解析器是可扩展的，也就是说，我们可以定义新的符号。

Lean的语法可以由用户在各个层面进行扩展和定制，从基本的 "mixfix "符号到自定义的阐述者。 事实上，所有内置的语法都是使用对用户开放的相同机制和API进行解析和处理的。 在本节中，我们将描述和解释各种扩展点。

虽然在编程语言中引入新的符号是一个相对罕见的功能，有时甚至因为它有可能使代码变得模糊不清而被人诟病，但它是形式化的一个宝贵工具，可以在代码中简洁地表达各自领域的既定惯例和符号。 除了基本的符号之外，Lean的能力是将普通的模板代码分解成（良好的）宏，并嵌入整个定制的特定领域语言（DSL），对子问题进行高效和可读的文本编码，这对程序员和证明工程师都有很大的好处。

###记号和优先级

最基本的语法扩展命令允许引入新的（或重载现有的）前缀、下缀和后缀运算符。
There is a third kind of implicit argument that is denoted with square brackets, ``[`` and ``]``. These are used for type classes, as explained in [Chapter Type Classes](./type_classes.md).

Notation
------------

Identifiers in Lean can include any alphanumeric characters, including Greek characters (other than ∀ , Σ , and λ , which, as we have seen, have a special meaning in the dependent type theory). They can also include subscripts, which can be entered by typing ``\_`` followed by the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

Lean's syntax can be extended and customized by users at every level, ranging from basic "mixfix" notations to custom elaborators.  In fact, all builtin syntax is parsed and processed using the same mechanisms and APIs open to users.  In this section, we will describe and explain the various extension points.

While introducing new notations is a relatively rare feature in programming languages and sometimes even frowned upon because of its potential to obscure code, it is an invaluable tool in formalization for expressing established conventions and notations of the respective field succinctly in code.  Going beyond basic notations, Lean's ability to factor out common boilerplate code into (well-behaved) macros and to embed entire custom domain specific languages (DSLs) to textually encode subproblems efficiently and readably can be of great benefit to both programmers and proof engineers alike.

### Notations and Precedence

The most basic syntax extension commands allow introducing new (or overloading existing) prefix, infix, and postfix operators.

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
# set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

After the initial command name describing the operator kind (its "fixity"), we give the *parsing precedence* of the operator preceded by a colon `:`, then a new or existing token surrounded by double quotes (the whitespace is used for pretty printing), then the function this operator should be translated to after the arrow `=>`.

The precedence is a natural number describing how "tightly" an operator binds to its arguments, encoding the order of operations.  We can make this more precise by looking at the commands the above unfold to:

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

It turns out that all commands from the first code block are in fact command *macros* translating to the more general `notation` command. We will learn about writing such macros below.  Instead of a single token, the `notation` command accepts a mixed sequence of tokens and named term placeholders with precedences, which can be referenced on the right-hand side of `=>` and will be replaced by the respective term parsed at that position.  A placeholder with precedence `p` accepts only notations with precedence at least `p` in that place. Thus the string `a + b + c` cannot be parsed as the equivalent of `a + (b + c)` because the right-hand side operand of an `infixl` notation has precedence one greater than the notation itself.  In contrast, `infixr` reuses the notation's precedence for the right-hand side operand, so `a ^ b ^ c` *can* be parsed as `a ^ (b ^ c)`.  Note that if we used `notation` directly to introduce an infix notation like

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

where the precedences do not sufficiently determine associativity, Lean's parser will default to right associativity.  More precisely, Lean's parser follows a local *longest parse* rule in the presence of ambiguous grammars: when parsing the right-hand side of `a ~` in `a ~ b ~ c`, it will continue parsing as long as possible (as the current precedence allows), not stopping after `b` but parsing `~ c` as well. Thus the term is equivalent to `a ~ (b ~ c)`.

As mentioned above, the `notation` command allows us to define arbitrary *mixfix* syntax freely mixing tokens and placeholders.

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

Placeholders without precedence default to `0`, i.e. they accept notations of any precedence in their place.
If two notations overlap, we again apply the longest parse rule:

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

The new notation is preferred to the binary notation since the latter, before chaining, would stop parsing after `1 + 2`.  If there are multiple notations accepting the same longest parse, the choice will be delayed until elaboration, which will fail unless exactly one overload is type correct.


Coercions
---------

In Lean, the type of natural numbers, ``Nat``, is different from the type of integers, ``Int``. But there is a function ``Int.ofNat`` that embeds the natural numbers in the integers, meaning that we can view any natural number as an integer, when needed. Lean has mechanisms to detect and insert *coercions* of this sort.

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

Displaying Information
----------------------

There are a number of ways in which you can query Lean for information about its current state and the objects and theorems that are available in the current context. You have already seen two of the most common ones, ``#check`` and ``#eval``. Remember that ``#check`` is often used in conjunction with the ``@`` operator, which makes all of the arguments to a theorem or definition explicit. In addition, you can use the ``#print`` command to get information about any identifier. If the identifier denotes a definition or theorem, Lean prints the type of the symbol, and its definition. If it is a constant or an axiom, Lean indicates that fact, and shows the type.

```lean
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
```

Setting Options
---------------

Lean maintains a number of internal variables that can be set by users to control its behavior. The syntax for doing so is as follows:

```
set_option <name> <value>
```

One very useful family of options controls the way Lean's *pretty- printer* displays terms. The following options take an input of true or false:

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

As an example, the following settings yield much longer output:

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

The command ``set_option pp.all true`` carries out these settings all at once, whereas ``set_option pp.all false`` reverts to the previous values. Pretty printing additional information is often very useful when you are debugging a proof, or trying to understand a cryptic error message. Too much information can be overwhelming, though, and Lean's defaults are generally sufficient for ordinary interactions.



<!--
Elaboration Hints
-----------------

When you ask Lean to process an expression like ``λ x y z, f (x + y) z``, you are leaving information implicit. For example, the types of ``x``, ``y``, and ``z`` have to be inferred from the context, the notation ``+`` may be overloaded, and there may be implicit arguments to ``f`` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as *type class resolution*. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function ``f`` has type ``Π {α : Type*}, α → α → α`` and Lean is trying to parse the expression ``f n``, where ``n`` can be inferred to have type ``nat``. Then it is clear that the implicit argument ``α`` has to be ``nat``. However, some inference problems are *higher order*. For example, the substitution operation for equality, ``eq.subst``, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

Now suppose we are given ``a b : ℕ`` and ``h₁ : a = b`` and ``h₂ : a * b > a``. Then, in the expression ``eq.subst h₁ h₂``, ``P`` could be any of the following:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

In other words, our intent may be to replace either the first or second ``a`` in ``h₂``, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute ``[reducible]``, ``[semireducible]``, or ``[irreducible]``. Definitions are marked ``[semireducible]`` by default. A definition with the ``[reducible]`` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the ``[irreducible]`` attribute. Theorems are marked ``[irreducible]`` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the ``local`` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked ``[elab_with_expected_type]``, ``[elab_simple]``. or ``[elab_as_eliminator]``. When applied to a definition ``f``, these bear on elaboration of an expression ``f a b c ...`` in which ``f`` is applied to arguments. With the default attribute, ``[elab_with_expected_type]``, the arguments ``a``, ``b``, ``c``, ... are elaborating using information about their expected type, inferred from ``f`` and the previous arguments. In contrast, with ``[elab_simple]``, the arguments are elaborated from left to right without propagating information about their types. The last attribute, ``[elab_as_eliminator]``, is commonly used for eliminators like recursors, induction principles, and ``eq.subst``. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the ``local`` modifier to limit their scope. Moreover, using the ``@`` symbol in front of an identifier in an expression instructs the elaborator to use the ``[elab_simple]`` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, ``@@``, which leaves parameters before the first higher-order parameter implicit. For example, ``@@eq.subst`` leaves the type of the equation implicit, but makes the context of the substitution explicit.

-->

使用库
-----------------

为了有效地使用Lean，你将不可避免地需要使用库中的定义和定理。回想一下，文件开头的``import``命令会从其他文件中导入之前编译的结果，而且导入是传递的；如果你导入了``Foo``，``Foo``又导入了``Bar``，那么``Bar``的定义和定理也可以被你利用。但是打开一个命名空间的行为，提供了更短的名字，并没有延续下去。在每个文件中，你需要打开你想使用的命名空间。

一般来说，你必须熟悉库和它的内容，这样你就知道有哪些定理、定义、符号和资源可供你使用。下面我们将看到Lean的编辑器模式也可以帮助你找到你需要的东西，但直接研究库的内容往往是不可避免的。Lean的标准库可以在网上找到，在GitHub上。

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)

你可以使用GitHub的浏览器界面查看这些目录和文件的内容。如果你在自己的电脑上安装了Lean，你可以在``lean``文件夹中找到这个库，用你的文件管理器探索它。每个文件顶部的注释标题提供了额外的信息。

Lean库的开发者遵循一般的命名准则，以便于猜测你所需要的定理的名称，或者在支持Lean模式的编辑器中用Tab自动补全来找到它，这将在下一节讨论。标识符一般是``camelCase``，而类型是`CamelCase`。对于定理的名称，我们依靠描述性的名称，其中不同的组成部分用`_`分开。通常情况下，定理的名称只是描述结论。

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

Remember that identifiers in Lean can be organized into hierarchical namespaces. For example, the theorem named ``le_of_succ_le_succ`` in the namespace ``Nat`` has full name ``Nat.le_of_succ_le_succ``, but the shorter name is made available by the command ``open Nat`` (for names not marked as `protected`). We will see in [Chapter Inductive Types](./inductive_types.md) and [Chapter Structures and Records](./structures_and_records.md) that defining structures and inductive data types in Lean generates associated operations, and these are stored in a namespace with the same name as the type under definition. For example, the product type comes with the following operations:

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

The first is used to construct a pair, whereas the next two, ``Prod.fst`` and ``Prod.snd``, project the two elements. The last, ``Prod.rec``, provides another mechanism for defining functions on a product in terms of a function on the two components. Names like ``Prod.rec`` are *protected*, which means that one has to use the full name even when the ``Prod`` namespace is open.

With the propositions as types correspondence, logical connectives are also instances of inductive types, and so we tend to use dot notation for them as well:

```lean
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
```

Auto Bound Implicit Arguments
-----------------

In the previous section, we have shown how implicit arguments make functions more convenient to use.
However, functions such as `compose` are still quite verbose to define. Note that the universe
polymorphic `compose` is even more verbose than the one previously defined.

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

You can avoid the `universe` command by providing the universe parameters when defining `compose`.

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

Lean 4 supports a new feature called *auto bound implicit arguments*. It makes functions such as `compose` much more convenient to write. When Lean processes the header of a declaration, any unbound identifier is automatically added as an implicit argument *if* it is a single lower case or greek letter. With this feature we can write `compose` as

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```
Note that Lean inferred a more general type using `Sort` instead of `Type`.

Although we love this feature and use it extensively when implementing Lean, we realize some users may feel uncomfortable with it. Thus, you can disable it using the command `set_option autoBoundImplicitLocal false`.

```lean
set_option autoBoundImplicitLocal false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

Implicit Lambdas
---------------

In Lean 3 stdlib, we find many [instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39) of the dreadful `@`+`_` idiom. It is often used when we the expected type is a function type with implicit arguments, and we have a constant (`reader_t.pure` in the example) which also takes implicit arguments. In Lean 4, the elaborator automatically introduces lambdas for consuming implicit arguments. We are still exploring this feature and analyzing its impact, but the experience so far has been very positive. Here is the example from the link above using Lean 4 implicit lambdas.

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

Users can disable the implicit lambda feature by using `@` or writing a lambda expression with `{}` or `[]` binder annotations.  Here are few examples

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

Sugar for Simple Functions
-------------------------

In Lean 3, we can create simple functions from infix operators by using parentheses. For example, `(+1)` is sugar for `fun x, x + 1`. In Lean 4, we generalize this notation using `·` As a placeholder. Here are a few examples:

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

As in Lean 3, the notation is activated using parentheses, and the lambda abstraction is created by collecting the nested `·`s. The collection is interrupted by nested parentheses. In the following example, two different lambda expressions are created.

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

Named Arguments
---------------

Named arguments enable you to specify an argument for a parameter by matching the argument with its name rather than with its position in the parameter list.  If you don't remember the order of the parameters but know their names, you can send the arguments in any order. You may also provide the value for an implicit parameter when Lean failed to infer it. Named arguments also improve the readability of your code by identifying what each argument represents.

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

In the following examples, we illustrate the interaction between named and default arguments.

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

You can use `..` to provide missing explicit arguments as `_`. This feature combined with named arguments is useful for writing patterns. Here is an example:

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | add    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

Ellipses are also useful when explicit argument can be automatically inferred by Lean, and we want to avoid a sequence of `_`s.

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
