使用Lean进行工作
=====================

你现在已经熟悉了依值类型论的基本原理，它既是一种定义数学对象的语言，也是一种构造证明的语言。现在你缺少一个定义新数据类型的机制。下一章介绍*归纳数据类型*的概念来帮你完成这个目标。但首先，在这一章中，我们从类型论的机制中抽身出来，探索与Lean交互的一些实用性问题。

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

Lean的主要功能是把用户的输入翻译成形式化的表达式，由内核检查其正确性，然后存储在环境中供以后使用。但是有些命令对环境有其他的影响，或者给环境中的对象分配属性，定义符号，或者声明类型族的实例，如[类型族](./type_classes.md)一章所述。这些命令大多具有全局效应，也就是说，它们不仅在当前文件中保持有效，而且在任何导入它的文件中也保持有效。然而，这类命令通常支持``local``修饰符，这表明它们只在当前``section``或``namespace``关闭前或当前文件结束前有效。

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

另一个例子，我们可以使用`instance`命令来给`isPrefix`关系分配符号`≤`。该命令将在[类型族](./type_classes.md)中解释，它的工作原理是给相关定义分配一个`[instance]`属性。

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

还有第三种隐式参数，用方括号表示，``[``和``]``。这些是用于类型族的，在[类型族](./type_classes.md)中解释。

符号
------------

Lean中的标识符可以包括任何字母数字字符，包括希腊字母（除了∀、Σ和λ，它们在依值类型论中有特殊的含义）。它们还可以包括下标，可以通过输入``\_``，然后再输入所需的下标字符。

Lean的解析器是可扩展的，也就是说，我们可以定义新的符号。

Lean的语法可以由用户在各个层面进行扩展和定制，从基本的“mixfix”符号到自定义的繁饰器。事实上，所有内置的语法都是使用对用户开放的相同机制和API进行解析和处理的。 在本节中，我们将描述和解释各种扩展点。

虽然在编程语言中引入新的符号是一个相对罕见的功能，有时甚至因为它有可能使代码变得模糊不清而被人诟病，但它是形式化的一个宝贵工具，可以在代码中简洁地表达各自领域的既定惯例和符号。 除了基本的符号之外，Lean的能力是将普通的样板代码分解成（良好的）宏，并嵌入整个定制的特定领域语言（DSL，domain specific language），对子问题进行高效和可读的文本编码，这对程序员和证明工程师都有很大的好处。

### 符号和优先级

最基本的语法扩展命令允许引入新的（或重载现有的）前缀、下缀和后缀运算符：

```lean
infixl:65   " + " => HAdd.hAdd  -- 左结合
infix:50    " = " => Eq         -- 非结合
infixr:80   " ^ " => HPow.hPow  -- 右结合
prefix:100  "-"   => Neg.neg
set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

句法：

运算符种类（其“结合方式”） : 解析优先级 "新的或现有的符号" => 这个符号应该翻译成的函数

优先级是一个自然数，描述一个运算符与它的参数结合的“紧密程度”，编码操作的顺序。我们可以通过查看上述展开的命令来使之更加精确：

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

事实证明，第一个代码块中的所有命令实际上都是命令*宏*，翻译成更通用的`notation`命令。我们将在下面学习如何编写这种宏。 `notation`命令不接受单一的记号，而是接受一个混合的记号序列和有优先级的命名项占位符，这些占位符可以在`=>`的右侧被引用，并将被在该位置解析的相应项所取代。 优先级为`p`的占位符在该处只接受优先级至少为`p`的记号。因此，字符串`a + b + c`不能被解析为等同于`a + (b + c)`，因为`infixl`符号的右侧操作数的优先级比该符号本身大。 相反，`infixr`重用了符号右侧操作数的优先级，所以`a ^ b ^ c` *可以*被解析为`a ^ (b ^ c)`。 注意，如果我们直接使用`notation`来引入一个infix符号，如

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

在上文没有充分确定结合规则的情况下，Lean的解析器将默认为右结合。 更确切地说，Lean的解析器在存在模糊语法的情况下遵循一个局部的*最长解析*规则：当解析`a ~`中`a ~ b ~ c`的右侧时，它将继续尽可能长的解析（在当前的上下文允许的情况下），不在`b`之后停止，而是同时解析`~ c`。因此该术语等同于`a ~ (b ~ c)`。

如上所述，`notation`命令允许我们定义任意的*mixfix*语法，自由地混合记号和占位符。

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

没有优先级的占位符默认为`0`，也就是说，它们接受任何优先级的符号来代替它们。如果两个记号重叠，我们再次应用最长解析规则：

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

新的符号比二进制符号要好，因为后者在连锁之前，会在`1 + 2`之后停止解析。 如果有多个符号接受同一个最长的解析，选择将被推迟到阐述，这将失败，除非正好有一个重载是类型正确的。

强制转换
---------

在Lean中，自然数的类型``Nat``，与整数的类型``Int``不同。但是有一个函数`Int.ofNat``将自然数嵌入整数中，这意味着我们可以在需要时将任何自然数视为整数。Lean有机制来检测和插入这种*强制转换*。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

显示信息
----------------------

有很多方法可以让你查询Lean的当前状态以及当前上下文中可用的对象和定理的信息。你已经看到了两个最常见的方法，`#check`和`#eval`。请记住，`#check`经常与`@`操作符一起使用，它使定理或定义的所有参数显式化。此外，你可以使用`#print`命令来获得任何标识符的信息。如果标识符表示一个定义或定理，Lean会打印出符号的类型，以及它的定义。如果它是一个常数或公理，Lean会指出它并显示其类型。

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

设置选项
---------------

Lean维护着一些内部变量，用户可以通过设置这些变量来控制其行为。语法如下：

```
set_option <name> <value>
```

有一系列非常有用的选项可以控制Lean的*漂亮打印机*显示项的方式。下列选项的输入值为真或假：

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

命令``set_option pp.all true``一次性执行这些设置，而``set_option pp.all false``则恢复到之前的值。当你调试一个证明，或试图理解一个神秘的错误信息时，漂亮地打印额外的信息往往是非常有用的。不过太多的信息可能会让人不知所措，Lean的默认值一般来说对普通的交互是足够的。

> 译者注：在Lean3的教程中有一节“Elaboration Hints”，在本教程中被注释掉了。有兴趣的读者可以去查阅。

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

Lean中的标识符可以被组织到分层的命名空间中。例如，命名空间``Nat``中名为``le_of_succ_le_succ``的定理有全称``Nat.le_of_succ_le_succ``，但较短的名称可由命令``open Nat``提供（对于未标记为`protected`的名称）。我们将在[归纳类型](./inductive_types.md)和[结构体和记录](./structures_and_records.md)中看到，在Lean中定义结构体和归纳数据类型会产生相关操作，这些操作存储在与被定义类型同名的命名空间。例如，乘积类型带有以下操作：

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

第一个用于构建一个对，而接下来的两个，``Prod.fst``和``Prod.snd``，投影两个元素。最后一个，``Prod.rec``，提供了另一种机制，用两个元素的函数来定义乘积上的函数。像``Prod.rec``这样的名字是*受保护*的，这意味着即使``Prod``名字空间是打开的，也必须使用全名。

由于命题即类型的对应原则，逻辑连接词也是归纳类型的实例，因此我们也倾向于对它们使用点符号：

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

自动约束隐参数
-----------------

在上一节中，我们已经展示了隐参数是如何使函数更方便使用的。然而，像`compose`这样的函数在定义时仍然相当冗长。宇宙多态的`compose`比之前定义的函数还要啰嗦。

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

你可以通过在定义`compose`时提供宇宙参数来避免使用`universe`命令。

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

Lean 4支持一个名为*自动约束隐参数*的新特性。它使诸如`compose`这样的函数在编写时更加方便。当Lean处理一个声明的头时，*如果*它是一个小写字母或希腊字母，任何未约束的标识符都会被自动添加为隐式参数。有了这个特性，我们可以把`compose`写成

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

请注意，Lean使用`Sort`而不是`Type`推断出了一个更通用的类型。

虽然我们很喜欢这个功能，并且在实现Lean时广泛使用，但我们意识到有些用户可能会对它感到不舒服。因此，你可以使用`set_option autoBoundImplicitLocal false`命令将其禁用。

```lean
set_option autoBoundImplicitLocal false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

隐式Lambda
---------------

在Lean 3 stdlib中，我们发现了许多[例子](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39)包含丑陋的`@`+`_`惯用法。当我们的预期类型是一个带有隐参数的函数类型，而我们有一个常量（例子中的`reader_t.pure`）也需要隐参数时，就会经常使用这个惯用法。在Lean 4中，繁饰器自动引入了lambda来消除隐参数。我们仍在探索这一功能并分析其影响，但到目前为止的结果是非常积极的。下面是上面链接中使用Lean 4隐式lambda的例子。

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

用户可以通过使用`@`或用包含`{}`或`[]`的约束标记编写的lambda表达式来禁用隐式lambda功能。下面是几个例子

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

简单函数语法糖
-------------------------

在Lean 3中，我们可以通过使用小括号从infix运算符中创建简单的函数。例如，`(+1)`是`fun x, x + 1`的语法糖。在Lean 4中，我们用`·`作为占位符来扩展这个符号。这里有几个例子：

```lean
namespace ex3
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

如同在Lean 3中，符号是用圆括号激活的，lambda抽象是通过收集嵌套的`·`创建的。这个集合被嵌套的小括号打断。在下面的例子中创建了两个不同的lambda表达式。

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

命名参数
---------------

命名参数使你可以通过用参数的名称而不是参数列表中的位置来指定参数。 如果你不记得参数的顺序但知道它们的名字，你可以以任何顺序传入参数。当Lean未能推断出一个隐参数时，你也可以提供该参数的值。命名参数还可以通过识别每个参数所代表的内容来提高你的代码的可读性。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

在下面的例子中，我们说明了命名参数和默认参数之间的交互。

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

你可以使用`..`来提供缺少的显式参数作为`_`。这个功能与命名参数相结合，对编写模式很有用。下面是一个例子：

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

当显式参数可以由Lean自动推断时，省略号也很有用，而我们想避免一连串的`_`。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
