归纳类型
===============

我们已经看到Lean的形式基础包括基本类型，``Prop, Type 0, Type 1, Type 2, ...``，并允许形成依赖函数类型，``(x : α) → β``。在例子中，我们还使用了额外的类型，如``Bool``、``Nat``和``Int``，以及类型构造子，如``List``和乘积``×``。事实上，在Lean的库中，除了宇宙之外的每一个具体类型和除了依赖箭头之外的每一个类型构造子都是一个被称为*归纳类型*的类型构造的一般类别的实例。值得注意的是，仅用类型宇宙、依赖箭头类型和归纳类型就可以构建一个内涵丰富的数学大厦；其他一切都源于这些。

直观地说，一个归纳类型是由一个指定的构造子列表建立起来的。在Lean中，指定这种类型的语法如下：

```
    inductive Foo where
      | constructor₁ : ... → Foo
      | constructor₂ : ... → Foo
      ...
      | constructorₙ : ... → Foo
```

我们的直觉是，每个构造子都指定了一种建立新的对象``Foo``的方法，可能是由以前构造的值构成。``Foo``类型只不过是由以这种方式构建的对象组成。归纳式声明中的第一个字符也可以用逗号而不是``|``来分隔构造子。

我们将在下面看到，构造子的参数可以包括``Foo``类型的对象，但要遵守一定的“正向性”约束，即保证``Foo``的元素是自下而上构建的。粗略地说，每个`...`可以是由``Foo``和以前定义的类型构建的任何箭头类型，其中``Foo``如果出现，也只是作为依赖箭头类型的“目标”。

我们将提供一些归纳类型的例子。我们还把上述方案稍微扩展，即相互定义的归纳类型，以及所谓的*归纳族*。

就像逻辑连接词一样，每个归纳类型都有引入规则，说明如何构造该类型的一个元素；还有消去规则，说明如何在另一个构造中“使用”该类型的一个元素。其实逻辑连接词也是归纳类型结构的例子。你已经看到了归纳类型的引入规则：它们只是在类型的定义中指定的构造子。消去规则提供了类型上的递归原则，其中也包括作为一种特殊情况的归纳原则。

在下一章中，我们将介绍Lean的函数定义包，它提供了更方便的方法来定义归纳类型上的函数并进行归纳证明。但是由于归纳类型的概念是如此的基本，我们觉得从低级的、实践的理解开始是很重要的。我们将从归纳类型的一些基本例子开始，然后逐步上升到更详细和复杂的例子。

枚举式类型
----------------

最简单的归纳类型是一个具有有限的、可枚举的元素列表的类型。

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

``inductive``命令创建了一个新类型``Weekday``。构造子都在``Weekday``命名空间中。

```lean
#check Weekday.sunday
#check Weekday.monday

open Weekday

#check sunday
#check monday
```

在声明`Weekday`的归纳类型时，可以省略`: Weekday`。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

把``sunday``、``monday``、... 、``saturday``看作是``Weekday``的不同元素，没有其他有区别的属性。消去规则``Weekday.rec``，与``Weekday``类型及其构造子一起定义。它也被称为*递归子*，它是使该类型“归纳”的原因：它允许我们通过给每个构造子分配相应的值来定义`Weekday`的函数。直观的说，归纳类型是由构造子详尽地生成的，除了它们构造的元素外，没有其他元素。

我们将使用`match`表达式来定义一个从``Weekday``到自然数的函数：

```lean
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3
```

注意，`match`表达式是使用你声明归纳类型时生成的*递归子* `Weekday.rec`来编译的。

```lean
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/
```

当声明一个归纳数据类型时，你可以使用`deriving Repr`来指示Lean生成一个函数，将`Weekday`对象转换为文本。这个函数被`#eval`命令用来显示`Weekday`对象。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```

将与某一结构相关的定义和定理归入同名的命名空间通常很有用。例如，我们可以将``numberOfDay``函数放在``Weekday``命名空间中。然后当我们打开命名空间时，我们就可以使用较短的名称。

我们可以定义从``Weekday``到``Weekday``的函数：

```lean
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```

我们如何证明``next (previous d) = d``对于任何Weekday``d``的一般定理？你可以使用`match`来为每个构造子提供一个证明：

```lean
def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```

用策略证明更简洁：

```lean
def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

下面的[归纳类型的策略](#_tactics_for_inductive_types)一节将介绍额外的策略，这些策略是专门为利用归纳类型而设计。

命题即类型的对应原则下，我们可以使用``match``来证明定理和定义函数。换句话说，通过案例证明是一种通过案例定义的方式，其中被“定义”的是一个证明而不是一段数据。

Lean库中的`Bool`类型是一个枚举类型的实例。

```lean
namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool
end Hidden
```

（为了运行这个例子，我们把它们放在一个叫做``Hidden``的命名空间中，这样像``Bool``这样的名字就不会和标准库中的 ``Bool``冲突。这是必要的，因为这些类型是Lean“启动工作”的一部分，在系统启动时被自动导入）。

作为一个练习，你应该思考这些类型的引入和消除规则的作用。作为进一步的练习，我们建议在``Bool``类型上定义布尔运算 ``and``、``or``、``not``，并验证其共性。注意，你可以使用`match`来定义像`and`这样的二元运算：

```lean
namespace Hidden
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
end Hidden
```

同样地，大多数等式可以通过引入合适的`match`，然后使用``rfl``来证明。

带参数的构造子
---------------------------

枚举类型是归纳类型的一种非常特殊的情况，其中构造子根本不需要参数。一般来说，“构造”可以依赖于数据，然后在构造参数中表示。考虑一下库中的乘积类型和求和类型的定义:

```lean
namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
end Hidden
```

请注意，我们在构造子的目标中没有包括类型``α``和``β``。同时，思考一下这些例子中发生了什么。乘积类型有一个构造子``Prod.mk``，它需要两个参数。要在``Prod α β``上定义一个函数，我们可以假设输入的形式是``Prod.mk a b``，而我们必须指定输出，用``a``和``b``来表示。我们可以用它来定义``Prod``的两个投影。注意，标准库定义的符号``α × β``表示``Prod α β``，``(a, b)``表示``Prod.mk a b``。

```lean
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
```

函数``fst``接收一个对``p``。``match``将`p`解释为一个对``Prod.mk a b``。还记得在[依赖类型论](./dependent_type_theory.md)中，为了给这些定义以最大的通用性，我们允许类型``α``和``β``属于任何宇宙。

下面是另一个例子，我们用递归子`Prod.casesOn`代替`match`。

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)
```

参数`motive`是用来指定你要构造的对象的类型，它是一个函数，因为它可能依赖于这个对。函数`cond`是一个布尔条件：`cond b t1 t2`，如果`b`为真，返回`t1`，否则返回`t2`。函数`prod_example`接收一个由布尔值`b`和一个数字`n`组成的对，并根据`b`为真或假返回`2 * n`或`2 * n + 1`。

相比之下，和类型有*两个*构造子`inl`和`inr`（表示“向左引入”和“向右引入”），每个都需要*一个*（显式的）参数。要在``Sum α β``上定义一个函数，我们必须处理两种情况：要么输入的形式是``inl a``，由此必须依据``a``指定一个输出值；要么输入的形式是``inr b``，由此必须依据``b``指定一个输出值。

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
Sum.casesOn (motive := fun _ => Nat) s
   (fun n => 2 * n)
   (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)
```

这个例子与前面的例子类似，但现在输入到`sum_example`的内容隐含了`inl n`或`inr n`的形式。在第一种情况下，函数返回``2 * n``，第二种情况下，它返回``2 * n + 1``。

注意，乘积类型取决于参数`α β : Type`，这些参数是构造子和`Prod`的参数。Lean会检测这些参数何时可以从构造子的参数或返回类型中推断出来，并在这种情况下使其隐式。

之后我们将看到当归纳类型的构造子从归纳类型本身获取参数时会发生什么。本节考虑的例子暂时不是这样：每个构造子只依赖于先前指定的类型。

注意到一个有多个构造子的类型是析取的：``Sum α β``的一个元素要么是``inl a``的形式，要么是``inl b``的形式。一个有多个参数的构造子引入了合取信息：从``Prod.mk a b``的元素``Prod α β``中我们可以提取``a``*和*``b``。一个任意的归纳类型可以包括这两个特征，通过拥有任意数量的构造子，每个构造子都需要任意数量的参数。

和函数定义一样，Lean的归纳定义语法可以让你把构造子的命名参数放在冒号之前：

```lean
namespace Hidden
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
end Hidden
```

这些定义的结果与本节前面给出的定义基本相同。

像``Prod``这样只有一个构造子的类型是纯粹的合取型：构造子只是将参数列表打包成一块数据，基本上是一个元组，后续参数的类型可以取决于初始参数的类型。我们也可以把这样的类型看作是一个“记录”或“结构体”。在Lean中，关键词``structure``可以用来同时定义这样一个归纳类型以及它的投影。

```lean
namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
end Hidden
```

这个例子同时介绍了归纳类型``Prod``，它的构造子``mk``，通常的消去子（``rec``和``recOn``），以及投影``fst``和``snd``。

如果你没有命名构造子，Lean使用`mk`作为默认值。例如，下面定义了一个记录，将一个颜色存储为RGB值的三元组：

```lean
structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

``yellow``的定义形成了有三个值的记录，而投影``Color.red``则返回红色成分。

如果你在每个字段之间加一个换行符，就可以不用括号。

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr
```

``structure``命令对于定义代数结构特别有用，Lean提供了大量的基础设施来支持对它们的处理。例如，这里是一个半群的定义：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

更多例子见[结构体和记录](./structures_and_records.md)。

我们已经讨论了依赖乘积类型`Sigma`：

```lean
namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
end Hidden
```

库中另两个归纳类型的例子：

```lean
namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
end Hidden
```

在依赖类型论的语义中，没有内置的部分函数的概念。一个函数类型``α → β``或一个依赖函数类型``(a : α) → β``的每个元素都被假定为在每个输入端有一个值。``Option``类型提供了一种表示部分函数的方法。`Option β`的一个元素要么是`none`，要么是`some b`的形式，用于某个值`b : β`。因此我们可以认为`α → Option β`类型的元素`f`是一个从`α`到`β`的部分函数：对于每一个`a : α`，`f a`要么返回`none`，表示`f a`是“未定义”，要么返回`some b`。

`Inhabited α`的一个元素只是证明了`α`有一个元素的事实。稍后，我们将看到``Inhabited``是Lean中*类型类*的一个例子：Lean可以被告知合适的基础类型是含有元素的，并且可以在此基础上自动推断出其他构造类型是含有元素的。

作为练习，我们鼓励你建立一个从``α``到``β``和``β``到``γ``的部分函数的组合概念，并证明其行为符合预期。我们也鼓励你证明``Bool``和``Nat``是含有元素的，两个含有元素的类型的乘积是含有元素的，以及到一个含有元素的类型的函数类型是含有元素的。

归纳定义的命题
--------------------------------

归纳定义的类型可以存在于任何类型宇宙中，包括最底层的类型，`Prop`。事实上，这正是逻辑连接词的定义方式。

```lean
namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
end Hidden
```

你应该想一想这些是如何产生你已经看到的引入和消去规则的。有一些规则规定了归纳类型的消去子可以“消去成”什么，或者说，哪些类型可以成为递归子的目标。粗略地说，``Prop``中的归纳类型的特点是，只能消去成``Prop``中的其他类型。这与以下理解是一致的：如果``p : Prop``，一个元素``hp : p``不携带任何数据。然而，这个规则有一个小的例外，我们将在[归纳族](#归纳族)y一节中讨论。

甚至存在量词也是归纳式定义的：

```lean
namespace Hidden
inductive Exists {α : Type u} (q : α → Prop) : Prop where
  | intro : ∀ (a : α), q a → Exists q
end Hidden
```

请记住，符号``∃ x : α, p``是``Exists (fun x : α => p)``的语法糖。

`False`, `True`, `And`和`Or`的定义与`Empty`, `Unit`, `Prod`和`Sum`的定义完全类似。不同的是，第一组产生的是`Prop`的元素，第二组产生的是`Type u`的元素，适用于某些`u`。类似地，``∃ x : α, p``是``Σ x : α, p``的``Prop``值的变体。

这里可以提到另一个归纳类型，表示为`{x : α // p}`，它有点像`∃ x : α, P`和`Σ x : α, P`之间的混合。

```lean
namespace Hidden
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
end Hidden
```

事实上，在Lean中，``Subtype``是用结构体命令定义的。

符号`{x : α // p x}`是``Subtype (fun x : α => p x)``的语法糖。它仿照集合理论中的子集表示法：`{x : α // p x}`表示具有属性`p`的`α`元素的集合。

定义自然数
----------------------------

到目前为止，我们所看到的归纳定义的类型都是“无趣的”：构造子打包数据并将其插入到一个类型中，而相应的递归子则解压数据并对其进行操作。当构造子作用于被定义的类型中的元素时，事情就变得更加有趣了。一个典型的例子是自然数``Nat``类型：

```lean
namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
end Hidden
```

有两个构造子，我们从``zero : Nat``开始；它不需要参数，所以我们一开始就有了它。相反，构造子`succ`只能应用于先前构造的`Nat`。将其应用于``zero``，得到``succ zero : Nat``。再次应用它可以得到`succ (succ zero) : Nat`，依此类推。直观地说，`Nat`是具有这些构造子的“最小”类型，这意味着它是通过从`zero`开始并重复应用`succ`这样无穷无尽地（并且自由地）生成的。

和以前一样，``Nat``的递归子被设计用来定义一个从``Nat``到任何域的依赖函数`f`，也就是一个`(n : nat) → motive n`的元素`f`，其中`motive : Nat → Sort u`。它必须处理两种情况：一种是输入为``zero``的情况，另一种是输入为 ``succ n``的情况，其中``n : Nat``。在第一种情况下，我们只需指定一个适当类型的目标值，就像以前一样。但是在第二种情况下，递归子可以假设在`n`处的`f`的值已经被计算过了。因此，递归子的下一个参数是以`n`和`f n`来指定`f (succ n)`的值。

如果我们检查递归子的类型，你会得到：

```lean
#check @Nat.rec
/-
  {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
-/
```

隐参数``motive``，是被定义的函数的陪域。在类型论中，通常说``motive``是消去/递归的*动机*，因为它描述了我们希望构建的对象类型。接下来的两个参数指定了如何计算零和后继的情况，如上所述。它们也被称为小前提``minor premises``。最后，``t : Nat``，是函数的输入。它也被称为大前提``major premise``。

`Nat.recOn`与`Nat.rec`类似，但大前提发生在小前提之前。

```
@Nat.recOn :
  {motive : Nat → Sort u}
  → (t : Nat)
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → motive t
```

例如，考虑自然数上的加法函数``add m n``。固定`m`，我们可以通过递归来定义`n`的加法。在基本情况下，我们将`add m zero`设为`m`。在后续步骤中，假设`add m n`的值已经确定，我们将`add m (succ n)`定义为`succ (add m n)`。

```lean
namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
end Hidden
```

将这些定义放入一个命名空间``Nat``是很有用的。然后我们可以继续在这个命名空间中定义熟悉的符号。现在加法的两个定义方程是成立的：

```lean
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
# end Hidden
```

我们将在[类型类](./type_classes.md)一章中解释``instance``命令如何工作。我们以后的例子将使用Lean自己的自然数版本。

然而，证明像``zero + m = m``这样的事实，需要用归纳法证明。如上所述，归纳原则只是递归原则的一个特例，当陪域``motive n``是``Prop``的一个元素。它代表了熟悉的归纳证明模式：要证明``∀ n, motive n``，首先要证明``motive 0``，然后对于任意的``n``，假设``ih : motive n``并证明``motive (succ n)``。

```lean
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc
       0 + succ n = succ (0 + n) := rfl
                _ = succ n       := by rw [ih])
```

请注意，当``Nat.recOn``在证明中使用时，它实际上是变相的归纳原则。``rewrite``和``simp``策略在这样的证明中往往非常有效。在这种情况下，证明可以化简成：

```lean
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
```

另一个例子，让我们证明加法结合律，``∀ m n k, m + n + k = m + (n + k)``。(我们定义的符号`+`是向左结合的，所以`m + n + k`实际上是`(m + n) + k`。) 最难的部分是确定在哪个变量上做归纳。由于加法是由第二个参数的递归定义的，``k``是一个很好的猜测，一旦我们做出这个选择，证明几乎是顺理成章的：

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc
          m + n + succ k = succ (m + n + k) := rfl
            _ = succ (m + (n + k)) := by rw [ih]
            _ = m + succ (n + k) := rfl
            _ = m + (n + succ k) := rfl)
```

你又可以化简证明：

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih]; done)
```

假设我们试图证明加法交换律。选择第二个参数做归纳法，我们可以这样开始：

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n = succ (m + n) := rfl
                  _ = succ (n + m) := by rw [ih]
                  _ = succ n +  m  := sorry)
```

在这一点上，我们看到我们需要另一个事实，即``succ (n + m) = succ n + m``。你可以通过对``m``的归纳来证明这一点：

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m = succ (succ n + m) := rfl
           _  = succ (succ (n + m))           := by rw [ih]
           _  = succ (n + succ m)             := rfl)
```

然后你可以用``succ_add``代替前面证明中的``sorry``。然而，证明可以再次压缩：

```lean
namespace Hidden
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp only [add_succ, succ_add, ih])
end Hidden
```

其他递归数据类型
--------------------------

让我们再考虑一些归纳定义类型的例子。对于任何类型``α``，在库中定义了``α``的元素列表``List α``类型。

```lean
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
end Hidden
```

一个``α``类型的元素列表，要么是空列表``nil``，要么是一个元素``h : α``，后面是一个列表``t : List α``。第一个元素`h`，通常被称为列表的“头”，最后一个`t`，被称为“尾”。

作为一个练习，请证明以下内容：

```lean
theorem append_nil (as : List α) : append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  sorry
```

还可以尝试定义函数``length : {α : Type u} → List α → Nat``，返回一个列表的长度，并证明它的行为符合我们的期望（例如，``length (append as bs) = length as + length bs``）。

另一个例子，我们可以定义二叉树的类型：

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

事实上，我们甚至可以定义可数多叉树的类型：

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

归纳类型的策略
---------------------------

归纳类型在Lean中有最根本的重要性，因此设计了一些方便使用的策略，这里讲几种。

``cases``策略适用于归纳定义类型的元素，正如其名称所示：它根据每个可能的构造子分解元素。在其最基本的形式中，它被应用于局部环境中的元素`x`。然后，它将目标还原为``x``被每个构成体所取代的情况。

```lean
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : ℕ ⊢ p (succ a)
```

还有一些额外的修饰功能。首先，``cases``允许你使用``with``子句来选择每个选项的名称。例如在下一个例子中，我们为``succ``的参数选择`m`这个名字，这样第二个情况就指的是`succ m`。更重要的是，cases策略将检测局部环境中任何依赖于目标变量的项目。它将这些元素还原，进行拆分，并重新引入它们。在下面的例子中，注意假设`h : n ≠ 0`在第一个分支中变成`h : 0 ≠ 0`，在第二个分支中变成`h : succ m ≠ 0`。

```lean
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl
```

``cases``可以用来产生数据，也可以用来证明命题。

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

再一次，cases将被还原，分隔，然后在背景中重新引入依赖。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

下面是一个带有参数的多个构造子的例子。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

每个构造子的备选项不需要按照构造子的声明顺序来求解。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

`with`的语法对于编写结构化证明很方便。Lean还提供了一个补充的`case`策略，它允许你专注于目标分配变量名。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

``case``策略很聪明，它将把构造子与适当的目标相匹配。例如，我们可以按照相反的顺序填充上面的目标：

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```

你也可以使用``cases``伴随一个任意的表达式。假设该表达式出现在目标中，cases策略将概括该表达式，引入由此产生的全称变量，并对其进行处理。

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

可以认为这是在说“把``m + 3 * k``是零或者某个数字的后继的情况拆开”。其结果在功能上等同于以下：

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

注意，表达式``m + 3 * k``被``generalize``删除了；重要的只是它的形式是``0``还是``succ a``。这种形式的``cases``*不会*恢复任何同时提到方程中的表达式的假设（在本例中是`m + 3 * k`）。如果这样的术语出现在一个假设中，而你也想对其进行概括，你需要明确地恢复``revert``它。

如果你所涉及的表达式没有出现在目标中，``cases``策略使用``have``来把表达式的类型放到上下文中。下面是一个例子：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

定理``Nat.lt_or_ge m n``说``m < n ∨ m ≥ n``，很自然地认为上面的证明是在这两种情况下的分割。在第一个分支中，我们有假设``h₁ : m < n``，在第二个分支中，我们有假设``h₂ : m ≥ n``。上面的证明在功能上等同于以下：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

在前两行之后，我们有``h : m < n ∨ m ≥ n``作为假设，我们只需在此基础上做cases。

下面是另一个例子，我们利用自然数相等的可判定性，对`m = n`和`m ≠ n`的情况进行拆分。

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```

如果你``open Classical``，你可以对任何命题使用排中律。但是使用[类型类](./type_classes.md)推理，Lean实际上可以找到相关的决策程序，这意味着你可以在可计算函数中使用情况拆分。

正如``cases``项可以用来进行分情况证明，``induction``项可以用来进行归纳证明。其语法与`cases`相似，只是参数只能是局部上下文中的一个项。下面是一个例子：

```lean
namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
end Hidden
```

和``cases``一样，我们可以使用``case``代替`with`。

```lean
namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
end Hidden
```

更多例子：

```lean
namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
end Hidden
```

`induction`策略也支持用户定义的具有多个目标（又称主前提）的归纳原则。

```lean
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
     have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
     match this with
     | Or.inl h₁ => exact absurd h h₁
     | Or.inr h₁ =>
       have hgt : y > x := Nat.gt_of_not_le h₁
       rw [← Nat.mod_eq_of_lt hgt] at hgt
       assumption
```

你也可以在策略中使用`match`符号：

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

为了方便起见，模式匹配已经被整合到诸如`intro`和`funext`等策略中。

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```

我们用最后一个策略来结束本节，这个策略旨在促进归纳类型的工作，即``injection``注入策略。归纳类型的元素是自由生成的，也就是说，构造子是注入式的，并且有不相交的作用范围。``injection``策略是为了利用这一事实：

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```

该策略的第一个实例在上下文中加入了``h' : succ m = succ n``，第二个实例加入了``h'' : m = n``。

``injection``策略还可以检测不同构造子被设置为相等时产生的矛盾，并使用它们来关闭目标。

```lean
open Nat


example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

如第二个例子所示，``contradiction``策略也能检测出这种形式的矛盾。

归纳族
------------------

我们几乎已经完成了对Lean所接受的全部归纳定义的描述。到目前为止，你已经看到Lean允许你用任何数量的递归构造子引入归纳类型。事实上，一个归纳定义可以引入一个有索引的归纳类型的*家族*。

归纳族是一个由以下形式的同时归纳定义的有索引的家族：

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```

与普通的归纳定义不同，它构造了某个``Sort u``的元素，更一般的版本构造了一个函数``... → Sort u``，其中``...``表示一串参数类型，也称为*索引*。然后，每个构造子都会构造一个家族中某个成员的元素。一个例子是``Vector α n``的定义，它是长度为``n``的``α``元素的向量的类型：

```lean
namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
end Hidden
```

注意，``cons``构造子接收``Vector α n``的一个元素，并返回``Vector α (n+1)``的一个元素，从而使用家族中的一个成员的元素来构建另一个成员的元素。

一个更奇特的例子是由Lean中相等类型的定义：

```lean
# namespace Hidden
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl {} : Eq a a
# end Hidden
```

对于每个固定的``α : Sort u``和``a : α``，这个定义构造了一个``Eq a x``的类型族，由``x : α``索引。然而，只有一个构造子`refl`，它是`Eq a a`的一个元素，构造子后面的大括号告诉Lean要把`refl`的参数明确化。直观地说，在`x`是`a`的情况下，构建`Eq a x`证明的唯一方法是使用自反性。请注意，`Eq a a`是`Eq a x`这个类型家族中唯一的类型。由Lean产生的消去规则如下：

```lean
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)
```

一个显著的事实是，所有关于相等的基本公理都来自构造子`refl`和消去子`Eq.rec`。然而，相等的定义是不典型的，见下一节的讨论。

递归子`Eq.rec`也被用来定义代换：

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
# end Hidden
```

可以使用`match`定义`subst`。

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
# end Hidden
```

实际上，Lean使用基于`Eq.rec`的定义来编译`match`表达式。、

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst
  -- ... subst.match_1 ...
#print subst.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...
# end Hidden
```

使用递归子或`match`与`h₁ : a = b`，我们可以假设`a`和`b`相同，在这种情况下，`p b`和`p a`相同。

证明``Eq``的对称和传递性并不难。在下面的例子中，我们证明`symm`，并留下`trans`和`congr`定理作为练习。

```lean
# namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
# end Hidden
```

在类型论文献中，有对归纳定义的进一步推广，例如，*归纳-递归*和*归纳-归纳*的原则。这些东西Lean暂不支持。

公理化细节
-----------------

我们已经通过例子描述了归纳类型和它们的语法。本节为那些对公理基础感兴趣的人提供额外的信息。

我们已经看到，归纳类型的构造子需要*参量*（parameter，与argument都有“参数”译义，为区别此处译为参量）——即在整个归纳构造过程中保持固定的参数——和*索引*，即同时在构造中的类型族的参数。每个构造子都应该有一个类型，其中的参数类型是由先前定义的类型、参量和索引类型以及当前正在定义的归纳族建立起来的。要求是，如果后者存在，它只*严格正向*出现。这意味着它所出现的构造子的任何参数都是一个依赖箭头类型，其中定义中的归纳类型只作为结果类型出现，其中的索引是以常量和先前的参数来给出。

既然一个归纳类型对于某些``u``来说存在于在``Sort u``中，那么我们有理由问*哪些*宇宙层次的``u``可以被实例化。归纳类型族 ``C``的定义中的每个构造子``c``的形式为

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

其中`a`是一列数据类型的参量，`b`是一列构造子的参数，`p[a, b]`是索引，用于确定构造所处的归纳族的元素。（请注意，这种描述有些误导，因为构造子的参数可以以任何顺序出现，只要依赖关系是合理的）。对``C``的宇宙层级的约束分为两种情况，取决于归纳类型是否被指定落在``Prop``（即``Sort 0``）。

我们首先考虑归纳类型*不*指定落在``Prop``的情况。那么宇宙等级`u'`被限制为满足以下条件：

> 对于上面的每个构造子`c`，以及序列`β[a]`中的每个`βk[a]`，如果`βk[a] : Sort v`，我们有`u`≥`v`。

换句话说，宇宙等级``u``被要求至少与代表构造子参数的每个类型的宇宙等级一样大。

当归纳类型被指定落在``Prop``中时，对构造子参数的宇宙等级没有任何限制。但是这些宇宙等级对消去规则有影响。一般来说，对于``Prop``中的归纳类型，消去规则的motive被要求在``Prop``中。

这最后一条规则有一个例外：当只有一个构造子，并且每个构造子参数都在`Prop`中或者是一个索引时，我们可以从一个归纳定义的`Prop`中消除到一个任意的`Sort`。直观的说，在这种情况下，消除并不利用任何信息，而这些信息并不是由参数类型被栖息这一简单的事实所提供的。这种特殊情况被称为*单子消除*（singleton elimination）。

我们已经在`Eq.rec`的应用中看到了单子消除的作用，这是归纳定义的相等类型的消去子。我们可以使用一个元素``h : Eq a b``来将一个元素``t' : p a``转换为``p b``，即使``p a``和``p b``是任意类型，因为转换并不产生新的数据；它只是重新解释了我们已经有的数据。单子消除法也用于异质等价和有根据的递归，这将在后面的章节中讨论。

相互和嵌套的归纳类型
---------------------------------

我们现在考虑两个经常有用的归纳类型的推广，Lean通过“编译”它们来支持上述更原始的归纳类型种类。换句话说，Lean解析了更一般的定义，在此基础上定义了辅助的归纳类型，然后使用辅助类型来定义我们真正想要的类型。下一章将介绍Lean的方程编译器，它需要有效地利用这些类型。尽管如此，在这里描述这些声明还是有意义的，因为它们是普通归纳定义的直接变形。

首先，Lean支持*相互定义*的归纳类型。这个想法是，我们可以同时定义两个（或更多）归纳类型，其中每个类型都指代其他类型。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

在这个例子中，同时定义了两种类型：一个自然数`n`如果是`0`或比`Even`多一个，就是`Odd`；如果是比`Odd`多一个，就是`Even`。在下面的练习中，要求你写出细节。

相互的归纳定义也可以用来定义有限树的符号，节点由`α`的元素标记：

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```

有了这个定义，我们可以通过给出一个``α``的元素和一个子树列表（可能是空的）来构造``Tree α``的元素。子树列表由`TreeList α`类型表示，它被定义为空列表`nil`，或者是一棵树的`cons`和`TreeList α`的一个元素。

然而，这个定义在工作中是不方便的。如果子树的列表是由``List (Tree α)``类型给出的，那就更好了，尤其是Lean的库中包含了一些处理列表的函数和定理。我们可以证明``TreeList α``类型与``List (Tree α)``是*同构*的，但是沿着这个同构关系来回翻译结果是很乏味的。

事实上，Lean允许我们定义我们真正想要的归纳类型：

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```

这就是所谓的*嵌套*归纳类型。它不属于上一节给出的归纳类型的严格规范，因为`Tree`不是严格意义上出现在`mk`的参数中，而是嵌套在`List`类型构造子中。然后Lean在其内核中自动建立了``TreeList α``和``List (Tree α)``之间的同构关系，并根据同构关系定义了``Tree``的构造子。

练习
---------

1. 尝试定义自然数的其他运算，如乘法、前继函数（定义`pred 0 = 0`）、截断减法（当`m`大于或等于`n`时，`n - m = 0`）和乘方。然后在我们已经证明的定理的基础上，尝试证明它们的一些基本属性。

由于其中许多已经在Lean的核心库中定义，你应该在一个名为``Hidden``或类似的命名空间中工作，以避免名称冲突。

2. 定义一些对列表的操作，如``length``函数或``reverse``函数。证明一些属性，比如下面这些。

  a. ``length (s ++ t) = length s + length t``

  b. ``length (reverse t) = length t``

  c. ``reverse (reverse t) = t``

3. 定义一个归纳数据类型，由以下构造子建立的项组成。

  - `const n`，一个表示自然数`n`的常数
  - `var n`，一个变量，编号为`n`
  - `plus s t`，表示`s`和`t`的总和
  - `times s t`，表示`s`和`t`的乘积

  递归地定义一个函数，根据变量的赋值来计算任何这样的项。

4. 同样，定义命题公式的类型，以及关于这类公式类型的函数：求值函数、衡量公式复杂性的函数，以及用另一个公式替代给定变量的函数。