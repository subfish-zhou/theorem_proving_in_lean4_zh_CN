依赖类型论
=====================

依赖类型论（Dependent type theory）是一种强大而富有表达力的语言，允许你表达复杂的数学断言，编写复杂的硬件和软件规范，并以自然和统一的方式对这两者进行推理。Lean是基于一个被称为*构造演算*（Calculus of Constructions）的依赖类型论的版本，它拥有一个可数的非累积性宇宙（non-cumulative universe）的层次结构以及递归类型（inductive type）。在本章结束时，你将学会一大部分。

## 普通类型论

“类型论”得名于其中每个表达式都有一个*类型*。举例：在一个给定的语境中，``x + 0``可能表示一个自然数，``f``可能表示一个定义在自然数上的函数。Lean中的自然数是任意精度的无符号整数。

这里的一些例子展示了如何声明对象以及检查其类型。

```lean
/- 定义一些常数 -/

def m : Nat := 1       -- m 是自然数
def n : Nat := 0
def b1 : Bool := true  -- b1 是布尔型
def b2 : Bool := false

/- 检查类型 -/

#check m            -- 输出: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- 求值（Evaluate） -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

位于``/-``和``-/``之间的文本组成了一个注释块，会被Lean的编译器忽略。类似地，两条横线`--`后面也是注释。注释块可以嵌套，这样就可以“注释掉”一整块代码，这和任何程序语言都是一样的。

``def``关键字声明工作环境中的新常量符号。在上面的例子中，`def m : Nat := 1`定义了一个`Nat`类型的新常量`m`，其值为`1`。``#check``命令要求Lean给出它的类型，用于向系统询问信息的辅助命令都以井号(#)开头。`#eval`命令让Lean计算给出的表达式。你应该试试自己声明一些常量和检查一些表达式的类型。

普通类型论的强大之处在于，你可以从其他类型中构建新的类型。例如，如果``a``和``b``是类型，``a -> b``表示从``a``到``b``的函数类型，``a × b``表示由``a``元素与``b``元素配对构成的类型，也称为*笛卡尔积*。注意`×`是一个Unicode符号，可以使用``\times``或简写``\tim``来输入。合理使用Unicode提高了易读性，所有现代编辑器都支持它。在Lean标准库中，你经常看到希腊字母表示类型，Unicode符号`→`是`->`的更紧凑版本。

```lean
#check Nat → Nat      -- 用"\to" or "\r"来打出这个箭头
#check Nat -> Nat     -- 也可以用 ASCII 符号

#check Nat × Nat      -- 用"\times"打出乘号
#check Prod Nat Nat   -- 换成ASCII 符号

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  结果和上一个一样

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- 一个“泛函”

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

同样，你应该自己尝试一些例子。

让我们看一些基本语法。你可以通过输入``\to``或者``\r``或者``\->``来输入``→``。你也可以就用ASCII码``->``，所以表达式``Nat -> Nat``和``Nat → Nat``意思是一样的，都表示以一个自然数作为输入并返回一个自然数作为输出的函数类型。Unicode符号``×``是笛卡尔积，用``\times``输入。小写的希腊字母``α``，``β``，和``γ``等等常用来表示类型变量，可以用``\a``，``\b``，和``\g``来输入。

这里还有一些需要注意的事情。第一，函数``f``应用到值``x``上写为``f x``(例：`Nat.succ 2`)。第二，当写类型表达式时，箭头是*右结合*的；例如，``Nat.add``的类型是``Nat → Nat → Nat``，等价于``Nat → (Nat → Nat)``。

因此你可以把``Nat.add``看作一个函数，它接受一个自然数并返回另一个函数，该函数接受一个自然数并返回一个自然数。在类型论中，把``Nat.add``函数看作接受一对自然数作为输入并返回一个自然数作为输出的函数通常会更方便。系统允许你“部分应用”函数``Nat.add``，比如``Nat.add 3``具有类型``Nat → Nat``，即``Nat.add 3``返回一个“等待”第二个参数``n``的函数，然后可以继续写``Nat.add 3 n``。

> 注：取一个类型为``Nat × Nat → Nat``的函数，然后“重定义”它，让它变成``Nat → Nat → Nat``类型，这个过程被称作*柯里化*（currying）。

如果你有``m : Nat``和``n : Nat``，那么``(m, n)``表示``m``和``n``组成的有序对，其类型为``Nat × Nat``。这个方法可以制造自然数对。反过来，如果你有``p : Nat × Nat``，之后你可以写``p.1 : Nat``和``p.2 : Nat``。这个方法用于提取它的两个组件。

## 类型作为对象

Lean所依据的依赖类型论对普通类型论的其中一项升级是，类型本身（如``Nat``和``Bool``这些东西）也是对象，因此也具有类型。

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

上面的每个表达式都是类型为``Type``的对象。你也可以为类型声明新的常量:

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

正如上面所示，你已经看到了一个类型为``Type → Type → Type``的函数例子，即笛卡尔积 `Prod`：

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

这里有另一个例子：给出任意类型``α``，那么类型``List α``是类型为``α``的元素的列表的类型。

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

看起来Lean中任何表达式都有一个类型，因此你可能会想到：``Type``自己的类型是什么？

```lean
#check Type      -- Type 1
```

实际上，你已经遇到了Lean系统的一个最微妙的方面：Lean的底层基础有无限的类型层次：

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

可以将``Type 0``看作是一个由“小”或“普通”类型组成的宇宙。然后，``Type 1``是一个更大的类型范围，其中包含``Type 0``作为一个元素，而``Type 2``是一个更大的类型范围，其中包含``Type 1``作为一个元素。这个列表是不确定的，所以对于每个自然数``n``都有一个``Type n``。``Type``是``Type 0``的缩写：

```lean
#check Type
#check Type 0
```

然而，有些操作需要在类型宇宙上具有*多态*（polymorphic）。例如，``List α``应该对任何类型的``α``都有意义，无论``α``存在于哪种类型的宇宙中。所以函数``List``有如下的类型：

```lean
#check List    -- Type u_1 → Type u_1
```

这里``u_1``是一个覆盖类型级别的变量。``#check``命令的输出意味着当``α``有类型``Type n``时，``List α``也有类型``Type n``。函数``Prod``具有类似的多态性：

```lean
#check Prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

你可以使用 `universe` 命令来声明宇宙变量，这样就可以定义定义多态常量：

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

可以通过在定义F时提供universe参数来避免使用universe命令：

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

## 函数抽象和求值

Lean提供 `fun` (或 `λ`)关键字用于从给定表达式创建函数，如下所示：

```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ 和 fun 是同义词
#check fun x : Nat => x + 5     -- 同上
#check λ x : Nat => x + 5       -- 同上
```

你可以通过传递所需的参数来计算lambda函数：

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

从另一个表达式创建函数的过程称为*lambda 抽象*。假设你有一个变量``x : α``和一个表达式``t : β``，那么表达式``fun (x : α) => t``或者``λ (x : α) => t``是一个类型为``α → β``的对象。这个从``α``到``β``的函数把任意``x``映射到``t``。

这有些例子：

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

Lean将这三个例子解释为相同的表达式；在最后一个表达式中，Lean可以从表达式`if not y then x + 1 else x + 2`推断``x``和``y``的类型。

一些数学上常见的函数运算的例子可以用lambda抽象的项来描述:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

看看这些表达式的意思。表达式``fun x : Nat => x``代表``Nat``上的恒等函数，表达式``fun x : Nat => true``表示一个永远输出``true``的常值函数，表达式``fun x : Nat => g (f x)``表示``f``和``g``的复合。一般来说，你可以省略类型注释，让Lean自己推断它。因此你可以写``fun x => g (f x)``来代替``fun x : Nat => g (f x)``。

你可以以函数作为参数，通过给它们命名`f`和`g`，你可以在实现中使用这些函数：

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

你还可以以类型作为参数：

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```

这个表达式表示一个接受三个类型``α``，``β``和``γ``和两个函数``g : β → γ``和``f : α → β``，并返回的``g``和``f``的复合的函数。(理解这个函数的类型需要理解依赖乘积类型，下面将对此进行解释。)

lambda表达式的一般形式是``fun x : α => t``，其中变量``x``是一个“约束变量”：它实际上是一个占位符，其“作用域”没有扩展到表达式``t``之外。例如，表达式``fun (b : β) (x : α) => b``中的变量``b``与前面声明的常量``b``没有任何关系。事实上，这个表达式表示的函数与``fun (u : β) (z : α) => u``是一样的。形式上，可以通过给约束变量重命名来使形式相同的表达式被看作是*alpha等价*的，也就是被认为是“一样的”。Lean认识这种等价性。

注意到项``t : α → β``应用到项``s : α``上导出了表达式``t s : β``。回到前面的例子，为清晰起见给约束变量重命名，注意以下表达式的类型:

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

表达式``(fun x : Nat =>  x) 1``的类型是``Nat``。实际上，应用``(fun x : Nat => x)``到``1``上返回的值是``1``。

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

稍后你将看到这些项是如何计算的。现在，请注意这是依赖类型论的一个重要特征：每个项都有一个计算行为，并支持“标准化”的概念。从原则上讲，两个可以化约为相同形式的项被称为“定义等价”。它们被Lean的类型检查器认为是“相同的”，并且Lean尽其所能地识别和支持这些识别结果。

Lean是个完备的编程语言。它有一个生成二进制可执行文件的编译器，和一个交互式解释器。你可以用`#eval`命令执行表达式，这也是测试你的函数的好办法。

> 注意到`#eval`和`#reduce`*不是*等价的。`#eval`命令首先把Lean表达式编译成中间表示（intermediate representation, IR）然后用一个解释器来执行这个IR。某些内建类型（例如，`Nat`、`String`、`Array`）在IR中有更有效率的表示。IR支持使用对Lean不透明的外部函数。
> ``#reduce``命令建立在一个化简引擎上，类似于在Lean的可信内核中使用的那个，它是负责检查和验证表达式和证明正确性的那一部分。它的效率不如``#eval``，且将所有外部函数视为不透明的常量。之后你将了解到这两个命令之间还有其他一些差异。

## 定义

``def``关键字提供了一个声明新对象的重要方式。

```lean
def double (x : Nat) : Nat :=
  x + x
```

这很类似其他编程语言中的函数。名字`double`被定义为一个函数，它接受一个类型为`Nat`的输入参数`x`，其结果是`x + x`，因此它返回类型`Nat`。然后你可以调用这个函数:

```lean
#eval double 3    -- 6
```

在这种情况下你可以把`def`想成一种`lambda`。下面给出了相同的结果：

```lean
def double :=
  fun (x : Nat) => x + x
```

当Lean有足够的信息来推断时，你可以省略类型声明。类型推断是Lean的重要组成部分:

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

定义的一般形式是``def foo : α := bar``，其中``α``是表达式``bar``返回的类型。Lean通常可以推断类型``α``，但是精确写出它可以澄清你的意图，并且如果定义的右侧没有匹配你的类型，Lean将标记一个错误。

`bar`可以是任何一个表达式，不只是一个lambda表达式。因此`def`也可以用于给一些值命名，例如：

```lean
def pi := 3.141592654
```

`def`可以接受多个输入参数。比如定义两自然数之和：

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

参数列表可以像这样分开写：

```lean
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

注意到这里我们使用了`double`函数来创建`add`函数的第一个参数。

你还可以在`def`中写一些更有趣的表达式：

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

你可能能猜到这个可以做什么。

还可以定义一个函数，该函数接受另一个函数作为输入。下面调用一个给定函数两次，将第一次调用的输出传递给第二次:

```lean
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

现在为了更抽象一点，你也可以指定类型参数等：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

这句代码的意思是：函数`compose`首先接受任何两个函数作为参数，这其中两个函数各自接受一个输入。类型`β → γ`和`α → β`意思是要求第二个函数的输出类型必须与第一个函数的输入类型匹配，否则这两个函数将无法复合。

`compose`再接受一个类型为`α`的参数作为第二个函数（这里叫做`f`）的输入，通过这个函数之后的返回结果类型为`β`，再作为第一个函数（这里叫做`g`）的输入。第一个函数返回类型为`γ`，这就是`compose`函数最终返回的类型。

`compose`可以在任意的类型`α β γ`上使用，它可以复合任意两个函数，只要前一个的输出类型是后一个的输入类型。举例：

```lean
-- def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
--  g (f x)
-- def double (x : Nat) : Nat :=
--  x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

## 局部定义


Lean还允许你使用``let``关键字来引入“局部定义”。表达式``let a := t1; t2``定义等价于把``t2``中所有的``a``替换成``t1``的结果。

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

这里``twice_double x``定义等价于``(x + x) * (x + x)``。

你可以连续使用多个``let``命令来进行多次替换：

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

换行可以省略分号``;``。

```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

表达式``let a := t1; t2``的意思很类似``(fun a => t2) t1``，但是这两者并不一样。前者中你要把``t2``中每一个``a``的实例考虑成``t1``的一个缩写。后者中``a``是一个变量，表达式``fun a => t2``不依赖于``a``的取值而可以单独具有意义。作为一个对照，考虑为什么下面的``foo``定义是合法的，但``bar``不行（因为在确定了``x``所属的``a``是什么之前，是无法让它``+ 2``的）。

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
# 变量和节

考虑下面这三个函数定义：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean提供``variable``指令来让这些声明变得紧凑：

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```

你可以声明任意类型的变量，不只是``Type``类型：

```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
输出结果表明所有三组定义具有完全相同的效果。

``variable``命令指示Lean将声明的变量作为约束变量插入定义中，这些定义通过名称引用它们。Lean足够聪明，它能找出定义中显式或隐式使用哪些变量。因此在写定义时，你可以将``α``、``β``、``γ``、``g``、``f``、``h``和``x``视为固定的对象，并让Lean自动抽象这些定义。

当以这种方式声明时，变量将一直保持存在，直到所处理的文件结束。然而，有时需要限制变量的作用范围。Lean提供了节标记``section``来实现这个目的：

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

当一个节结束后，变量不再发挥作用。

你不需要缩进一个节中的行。你也不需要命名一个节，也就是说，你可以使用一个匿名的``section`` /``end``对。但是，如果你确实命名了一个节，你必须使用相同的名字关闭它。节也可以嵌套，这允许你逐步增加声明新变量。

## 命名空间

Lean可以让你把定义放进一个“命名空间”（``namespace``）里，并且命名空间也是层次化的：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

当你声明你在命名空间``Foo``中工作时，你声明的每个标识符都有一个前缀``Foo.``。在打开的命名空间中，可以通过较短的名称引用标识符，但是关闭命名空间后，必须使用较长的名称。与`section`不同，命名空间需要一个名称。只有一个匿名命名空间在根级别上。

``open``命令使你可以在当前使用较短的名称。通常，当你导入一个模块时，你会想打开它包含的一个或多个命名空间，以访问短标识符。但是，有时你希望将这些信息保留在一个完全限定的名称中，例如，当它们与你想要使用的另一个命名空间中的标识符冲突时。因此，命名空间为你提供了一种在工作环境中管理名称的方法。

例如，Lean把和列表相关的定义和定理都放在了命名空间``List``之中。

```lean
#check List.nil
#check List.cons
#check List.map
```
``open List``命令允许你使用短一点的名字：

```lean
open List

#check nil
#check cons
#check map
```

像节一样，命名空间也是可以嵌套的：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```

关闭的命名空间可以之后重新打开，甚至是在另一个文件里：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

与节一样，嵌套的名称空间必须按照打开的顺序关闭。命名空间和节有不同的用途：命名空间组织数据，节声明变量，以便在定义中插入。节对于分隔``set_option``和``open``等命令的范围也很有用。

然而，在许多方面，``namespace ... end``结构块和``section ... end``表现出来的特征是一样的。尤其是你在命名空间中使用``variable``命令时，它的作用范围被限制在命名空间里。类似地，如果你在命名空间中使用``open``命令，它的效果在命名空间关闭后消失。

## 依赖类型论“依赖”着什么?

简单地说，类型可以依赖于参数。你已经看到了一个很好的例子：类型``List α``依赖于参数``α``，而这种依赖性是区分``List Nat``和``List Bool``的关键。另一个例子，考虑类型``Vector α n``，即长度为``n``的``α``元素的向量类型。这个类型取决于*两个*参数：向量中元素的类型``α : Type``和向量的长度``n : Nat``。

假设你希望编写一个函数``cons``，它在列表的开头插入一个新元素。``cons``应该有什么类型？这样的函数是*多态的*（polymorphic）：你期望``Nat``，``Bool``或任意类型``α``的``cons``函数表现相同的方式。因此，将类型作为``cons``的第一个参数是有意义的，因此对于任何类型``α``，``cons α``是类型``α``列表的插入函数。换句话说，对于每个``α``，``cons α``是将元素``a : α``插入列表``as : List α``的函数，并返回一个新的列表，因此有``cons α a as : List α``。

很明显，``cons α``具有类型``α → List α → List α``，但是``cons``具有什么类型？如果我们假设是``Type → α → list α → list α``，那么问题在于，这个类型表达式没有意义：``α``没有任何的所指，但它实际上指的是某个类型``Type``。换句话说，*假设*``α : Type``是函数的首个参数，之后的两个参数的类型是``α``和``List α``，它们依赖于首个参数``α``。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

这就是*依赖函数类型*，或者*依赖箭头类型*的一个例子。给定``α : Type``和``β : α → Type``，把``β``考虑成``α``之上的类型族，也就是说，对于每个``a : α``都有类型``β a``。在这种情况下，类型``(a : α) → β a``表示的是具有如下性质的函数``f``的类型：对于每个``a : α``，``f a``是``β a``的一个元素。换句话说，``f``返回值的类型取决于其输入。

注意到``(a : α) → β``对于任意表达式``β : Type``都有意义。当``β``的值依赖于``a``（例如，在前一段的表达式``β a``），``(a : α) → β``表示一个依赖函数类型。当``β``的值不依赖于``a``，``(a : α) → β``与类型``α → β``无异。实际上，在依赖类型论（以及Lean）中，``α → β``表达的意思就是当``β``的值不依赖于``a``时的``(a : α) → β``。【注】

> 译者注：在依赖类型论的数学符号体系中，依赖类型是用``Π``符号来表达的，在Lean 3中还使用这种表达，例如``Π x : α, β x``。Lean 4抛弃了这种对新手不友好的写法，但是沿袭了三代中另外两种意义更明朗的写法：``forall x : α, β x``和``∀ x : α, β x``。这几个表达式都和``(x : α) → β x``同义。但是个人感觉本教程这一段的讲法也对新手不友好，``(x : α) → β x``这种写法在引入“构造子”之后意义会更明朗一些（见下一个注释），当前反倒是``forall x : α, β x``这种写法更加清楚明白，在[量词与等价](./quantifiers_and_equality.md)一章中有更详细的说明。同时，依赖类型有着更丰富的引入动机，推荐读者寻找一些拓展读物。

回到列表的例子，你可以使用`#check`命令来检查下列的`List`函数。``@``符号以及圆括号和花括号之间的区别将在后面解释。

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

就像依赖函数类型``(a : α) → β a``通过允许``β``依赖``α``从而推广了函数类型``α → β``，依赖笛卡尔积类型``(a : α) × β a``同样推广了笛卡尔积``α × β``。依赖积类型又称为*sigma*类型，可写成`Σ a : α, β a`。你可以用`⟨a, b⟩`或者`Sigma.mk a b`来创建依赖对。

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```
函数`f`和`g`表达的是同样的函数。

## 隐参数

假设我们有一个列表的实现如下：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
```

然后，你可以建立一个自然数列表如下：

```lean
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```

由于构造子对类型是多态的【注】，我们需要重复插入类型``Nat``作为一个参数。但是这个信息是多余的：我们可以推断表达式``Lst.cons Nat 5 (Lst.nil Nat)``中参数``α``的类型，这是通过第二个参数``5``的类型是``Nat``来实现的。类似地，我们可以推断``Lst.nil Nat``中参数的类型，这是通过它作为函数``Lst.cons``的一个参数，且这个函数在这个位置需要接收的是一个具有``Lst α``类型的参数来实现的。

> 译者注：“构造子”（constructor）的概念前文未加解释，对类型论不熟悉的读者可能会困惑。它指的是一种“依赖类型的类型”，也可以看作“类型的构造器”，例如``λ α : α -> α``甚至可看成``⋆ -> ⋆``。当给``α``或者``⋆``赋予一个具体的类型时，这个表达式就成为了一个类型。前文中``(x : α) → β x``中的``β``就可以看成一个构造子，``(x : α)``就是传进的类型参数。原句“构造子对类型是多态的”意为给构造子中放入不同类型时它会变成不同类型。

这是依赖类型论的一个主要特征：项包含大量信息，而且通常可以从上下文推断出一些信息。在Lean中，我们使用下划线``_``来指定系统应该自动填写信息。这就是所谓的“隐参数”。

```lean
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs
```

然而，敲这么多下划线仍然很无聊。当一个函数接受一个通常可以从上下文推断出来的参数时，Lean允许你指定该参数在默认情况下应该保持隐式。这是通过将参数放入花括号来实现的，如下所示:

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

唯一改变的是变量声明中``α : Type u``周围的花括号。我们也可以在函数定义中使用这个技巧：

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

这使得``ident``的第一个参数是隐式的。从符号上讲，这隐藏了类型的说明，使它看起来好像``ident``只是接受任何类型的参数。事实上，函数``id``在标准库中就是以这种方式定义的。我们在这里选择一个非传统的名字只是为了避免名字的冲突。

``variable``命令也可以用这种技巧来来把变量变成隐式的：

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

Lean有非常复杂的机制来实例化隐参数，我们将看到它们可以用来推断函数类型、谓词，甚至证明。实例化这些“洞”或“占位符”的过程通常被称为*阐释*（elaboration）。隐参数的存在意味着有时可能没有足够的信息来精确地确定表达式的含义。像``id``或``List.nil``这样的表达式被认为是“多态的”，因为它可以在不同的上下文中具有不同的含义。

可以通过写``(e : T)``来指定表达式``e``的类型``T``。这就指导Lean的阐释器在试图解决隐式参数时使用值``T``作为``e``的类型。在下面的第二个例子中，这种机制用于指定表达式``id``和``List.nil``所需的类型:

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

Lean中数字是重载的，但是当数字的类型不能被推断时，Lean默认假设它是一个自然数。因此，下面的前两个``#check``命令中的表达式以同样的方式进行了阐释，而第三个``#check``命令将``2``解释为整数。

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

然而，有时我们可能会发现自己处于这样一种情况：我们已经声明了函数的参数是隐式的，但现在想显式地提供参数。如果``foo``是有隐参数的函数，符号``@foo``表示所有参数都是显式的该函数。

```lean
#check @id        -- {α : Type u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

第一个``#check``命令给出了标识符的类型``id``，没有插入任何占位符。而且，输出表明第一个参数是隐式的。