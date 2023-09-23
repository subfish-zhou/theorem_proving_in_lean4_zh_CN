量词与等价
========================

上一章介绍了构造包含命题连接词的证明方法。在本章中，我们扩展逻辑结构，包括全称量词和存在量词，以及等价关系。

全称量词
------------------------

如果``α``是任何类型，我们可以将``α``上的一元谓词``p``作为``α → Prop``类型的对象。在这种情况下，给定``x : α``， ``p x``表示断言``p``在``x``上成立。类似地，一个对象``r : α → α → Prop``表示``α``上的二元关系：给定``x y : α``，``r x y``表示断言``x``与``y``相关。

全称量词``∀ x : α, p x``表示，对于每一个``x : α``，``p x``成立。与命题连接词一样，在自然演绎系统中，“forall”有引入和消去规则。非正式地，引入规则是：

> 给定``p x``的证明，在``x : α``是任意的情况下，我们得到``∀ x : α, p x``的证明。

消去规则是：

> 给定``∀ x : α, p x``的证明和任何项``t : α``，我们得到``p t``的证明。

与蕴含的情况一样，命题即类型。回想依值箭头类型的引入规则:

> 给定类型为``β x``的项``t``，在``x : α``是任意的情况下，我们有``(fun x : α => t) : (x : α) → β x``。

消去规则：

> 给定项``s : (x : α) → β x``和任何项``t : α``，我们有``s t : β t``。

在``p x``具有``Prop``类型的情况下，如果我们用``∀ x : α, p x``替换``(x : α) → β x``，就得到构建涉及全称量词的证明的规则。

因此，构造演算用全称表达式来识别依值箭头类型。如果``p``是任何表达式，``∀ x : α, p``不过是``(x : α) → p``的替代符号，在``p``是命题的情况下，前者比后者更自然。通常，表达式``p``取决于``x : α``。回想一下，在普通函数空间中，我们可以将``α → β``解释为``(x : α) → β``的特殊情况，其中``β``不依赖于``x``。类似地，我们可以把命题之间的蕴涵``p → q``看作是``∀ x : p, q``的特殊情况，其中``q``不依赖于``x``。

下面是一个例子，说明了如何运用命题即类型对应规则。``∀``可以用``\forall``输入，也可以用前两个字母简写``\fo``。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

作为一种符号约定，我们给予全称量词尽可能最宽的优先级范围，因此上面例子中的假设中，需要用括号将``x``上的量词限制起来。证明``∀ y : α, p y``的标准方法是取任意的``y``，然后证明``p y``。这是引入规则。现在，给定``h``有类型``∀ x : α, p x ∧ q x``，表达式``h y``有类型``p y ∧ q y``。这是消去规则。取合取的左侧得到想要的结论``p y``。

只有约束变量名称不同的表达式被认为是等价的。因此，例如，我们可以在假设和结论中使用相同的变量``x``，并在证明中用不同的变量``z``实例化它:

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

再举一个例子，下面是关系``r``的传递性：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
```

当我们在值``a b c``上实例化``trans_r``时，我们最终得到``r a b → r b c → r a c``的证明。将此应用于“假设”``hab : r a b``，我们得到了``r b c → r a c``的一个证明。最后将它应用到假设``hbc``中，得到结论``r a c``的证明。

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

优点是我们可以简单地写``trans_r hab hbc``作为``r a c``的证明。一个缺点是Lean没有足够的信息来推断表达式``trans_r``和``trans_r hab``中的参数类型。第一个``#check``命令的输出是``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``，表示在本例中隐式参数未指定。

下面是一个用等价关系进行基本推理的例子:

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

为了习惯使用全称量词，你应该尝试本节末尾的一些练习。

依值箭头类型的类型规则，特别是全称量词，体现了``Prop``命题类型与其他对象的类型的不同。假设我们有``α : Sort i``和``β : Sort j``，其中表达式``β``可能依赖于变量``x : α``。那么``(x : α) → β``是``Sort (imax i j)``的一个元素，其中``imax i j``是``i``和``j``在``j``不为0时的最大值，否则为0。

其想法如下。如果``j``不是``0``，然后``(x : α) → β``是``Sort (max i j)``类型的一个元素。换句话说，从``α``到``β``的一类依值函数存在于指数为``i``和``j``最大值的宇宙中。然而，假设``β``属于``Sort 0``，即``Prop``的一个元素。在这种情况下，``(x : α) → β``也是``Sort 0``的一个元素，无论``α``生活在哪种类型的宇宙中。换句话说，如果``β``是一个依赖于``α``的命题，那么``∀ x : α, β``又是一个命题。这反映出``Prop``作为一种命题类型而不是数据类型，这也使得``Prop``具有“非直谓性”（impredicative）。

“直谓性”一词起源于20世纪初的数学基础发展，当时逻辑学家如庞加莱和罗素将集合论的悖论归咎于“恶性循环”：当我们通过量化一个集合来定义一个属性时，这个集合包含了被定义的属性。注意，如果``α``是任何类型，我们可以在``α``上形成所有谓词的类型``α → Prop``(``α``的“幂”类型)。Prop的非直谓性意味着我们可以通过``α → Prop``形成量化命题。特别是，我们可以通过量化所有关于``α``的谓词来定义``α``上的谓词，这正是曾经被认为有问题的循环类型。

等价
--------

现在让我们来看看在Lean库中定义的最基本的关系之一，即等价关系。在[归纳类型](inductive_types.md)一章中，我们将解释如何从Lean的逻辑框架中定义等价。在这里我们解释如何使用它。

等价关系的基本性质：反身性、对称性、传递性。

```lean
#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ?m.2 = ?m.3 → ?m.3 = ?m.2
#check Eq.trans   -- ?m.2 = ?m.3 → ?m.3 = ?m.4 → ?m.2 = ?m.4
```

通过告诉Lean不要插入隐参数(在这里显示为元变量)可以使输出更容易阅读。

```lean
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

``.{u}``告诉Lean实例化宇宙``u``上的常量。

因此，我们可以将上一节中的示例具体化为等价关系:

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

我们也可以使用简写：

```lean
example : a = d := (hab.trans hcb.symm).trans hcd
```

反身性比它看上去更强大。回想一下，在构造演算中，项有一个计算解释，可化简为相同形式的项会被逻辑框架视为相同的。因此，一些非平凡的恒等式可以通过自反性来证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : α) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

框架的这个特性非常重要，以至于库中为``Eq.refl _``专门定义了一个符号``rfl``：

```lean
variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

然而，等价不仅仅是一种关系。它有一个重要的性质，即每个断言都遵从等价性，即我们可以在不改变真值的情况下对表达式做等价代换。也就是说，给定``h1 : a = b``和``h2 : p a``，我们可以构造一个证明``p b``，只需要使用代换``Eq.subst h1 h2``。

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

第二个例子中的三角形是建立在``Eq.subst``和``Eq.symm``之上的宏，它可以通过``\t``来输入。

规则``Eq.subst``定义了一些辅助规则，用来执行更显式的替换。它们是为处理应用型项，即形式为``s t``的项而设计的。这些辅助规则是，使用``congrArg``来替换参数，使用``congrFun``来替换正在应用的项，并且可以同时使用``congr``来替换两者。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Lean的库包含大量通用的等式，例如：

```lean
variable (a b c d : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

``Nat.mul_add``和``Nat.add_mul``是``Nat.left_distrib``和``Nat.right_distrib``的代称。上面的属性是为自然数类型``Nat``声明的。

这是一个使用代换以及结合律、交换律和分配律的自然数计算的例子。

```lean
example (x y z : Nat) : x * (y + z) = x * y + x * z := Nat.mul_add x y z
example (x y z : Nat) : (x + y) * z = x * z + y * z := Nat.add_mul x y z
example (x y z : Nat) : x + y + z = x + (y + z) := Nat.add_assoc x y z

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

注意，``Eq.subst``的第二个隐式参数提供了将要发生代换的表达式上下文，其类型为``α → Prop``。因此，推断这个谓词需要一个*高阶合一*（higher-order unification）的实例。一般来说，确定高阶合一器是否存在的问题是无法确定的，而Lean充其量只能提供不完美的和近似的解决方案。因此，``Eq.subst``并不总是做你想要它做的事。宏``h ▸ e``使用了更有效的启发式方法来计算这个隐参数，并且在不能应用``Eq.subst``的情况下通常会成功。

因为等式推理是如此普遍和重要，Lean提供了许多机制来更有效地执行它。下一节将提供允许你以更自然和清晰的方式编写计算式证明的语法。但更重要的是，等式推理是由项重写器、简化器和其他种类的自动化方法支持的。术语重写器和简化器将在下一节中简要描述，然后在下一章中更详细地描述。

计算式证明
--------------------

一个计算式证明是指一串使用诸如等式的传递性等基本规则得到的中间结果。在Lean中，计算式证明从关键字``calc``开始，语法如下：

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
    '_'     'op_2'  <expr>_2  ':='  <proof>_2
     ...
    '_'     'op_n'  <expr>_n  ':='  <proof>_n

```

每个``<proof>_i``是``<expr>_{i-1} op_i <expr>_i``的证明。

例子：

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

这种写证明的风格在与`simp`和`rewrite`策略（tactic）结合使用时最为有效，这些策略将在下一章详细讨论。例如，用缩写`rw'表示重写，上面的证明可以写成如下。

```lean
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

本质上，``rw``策略使用一个给定的等式(它可以是一个假设、一个定理名称或一个复杂的项)来“重写”目标。如果这样做将目标简化为一种等式``t = t``，那么该策略将使用反身性来证明这一点。

重写可以一次应用一系列，因此上面的证明可以缩写为：

```lean
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

甚至这样：

```lean
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

相反，``simp``策略通过在项中以任意顺序在任何适用的地方重复应用给定的等式来重写目标。它还使用了之前声明给系统的其他规则，并明智地应用交换性以避免循环。因此，我们也可以如下证明定理:

```lean
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

我们将在下一章讨论``rw``和``simp``的变体。

``calc``命令可以配置为任何支持某种形式的传递性的关系。它甚至可以结合不同的关系。

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

使用``calc``，我们可以以一种更自然、更清晰的方式写出上一节的证明。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
        _ = x * x + y * x + (x + y) * y            := by rw [Nat.add_mul]
        _ = x * x + y * x + (x * y + y * y)        := by rw [Nat.add_mul]
        _ = x * x + y * x + x * y + y * y          := by rw [←Nat.add_assoc]
```

``Nat.add_assoc``之前的左箭头指挥重写以相反的方向使用等式。(你可以输入``\l``或ascii码``<-``。)如果追求简洁，``rw``和``simp``可以一次性完成这项工作:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]
```

存在量词
--------------------------

存在量词可以写成``exists x : α, p x``或``∃ x : α, p x``。这两个写法实际上在Lean的库中的定义为一个更冗长的表达式，``Exists (fun x : α => p x)``。

存在量词也有一个引入规则和一个消去规则。引入规则很简单：要证明``∃ x : α, p x``，只需提供一个合适的项``t``和对``p t``的证明即可。``∃``用``\exists``或简写``\ex``输入，下面是一些例子:

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro
```

当类型可从上下文中推断时，我们可以使用匿名构造子表示法``⟨t, h⟩``替换``Exists.intro t h``。

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

注意``Exists.intro``有隐参数：Lean必须在结论``∃ x, p x``中推断谓词``p : α → Prop``。这不是一件小事。例如，如果我们有``hg : g 0 0 = 0``和``Exists.intro 0 hg``，有许多可能的值的谓词``p``，对应定理``∃ x, g x x = x``，``∃ x, g x x = 0``，``∃ x, g x 0 = x``，等等。Lean使用上下文来推断哪个是合适的。下面的例子说明了这一点，在这个例子中，我们设置了选项``pp.explicit``为true，要求Lean打印隐参数。

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- 打印隐参数
#print gex1
#print gex2
#print gex3
#print gex4
```

我们可以将``Exists.intro``视为信息隐藏操作，因为它将断言的具体实例隐藏起来变成了存在量词。存在消去规则``Exists.elim``执行相反的操作。它允许我们从``∃ x : α, p x``证明一个命题``q``，通过证明对于任意值``w``时``p w``都能推出``q``。粗略地说，既然我们知道有一个``x``满足``p x``，我们可以给它起个名字，比如``w``。如果``q``没有提到``w``，那么表明``p w``能推出``q``就等同于表明``q``从任何这样的``x``的存在而推得。下面是一个例子:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

把存在消去规则和析取消去规则作个比较可能会带来一些启发。命题``∃ x : α, p x``可以看成一个对所有``α``中的元素``a``所组成的命题``p a``的大型析取。注意到匿名构造子``⟨w, hw.right, hw.left⟩``是嵌套的构造子``⟨w, ⟨hw.right, hw.left⟩⟩``的缩写。

存在式命题类型很像依值类型一节所述的sigma类型。给定``a : α``和``h : p a``时，项``Exists.intro a h``具有类型``(∃ x : α, p x) : Prop``，而``Sigma.mk a h``具有类型``(Σ x : α, p x) : Type``。``∃``和``Σ``之间的相似性是Curry-Howard同构的另一例子。

Lean提供一个更加方便的消去存在量词的途径，那就是通过``match``表达式。

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

``match``表达式是Lean功能定义系统的一部分，它提供了复杂功能的方便且丰富的表达方式。再一次，正是Curry-Howard同构让我们能够采用这种机制来编写证明。``match``语句将存在断言“析构”到组件``w``和``hw``中，然后可以在语句体中使用它们来证明命题。我们可以对match中使用的类型进行注释，以提高清晰度：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

我们甚至可以同时使用match语句来分解合取：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

Lean还提供了一个模式匹配的``let``表达式：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

这实际上是上面的``match``结构的替代表示法。Lean甚至允许我们在``fun``表达式中使用隐含的``match``：

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

我们将在[归纳和递归](./induction_and_recursion.md)一章看到所有这些变体都是更一般的模式匹配构造的实例。

在下面的例子中，我们将``even a``定义为``∃ b, a = 2*b``，然后我们证明两个偶数的和是偶数。

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2  := by rw [hw1, hw2]
          _   = 2*(w1 + w2)      := by rw [Nat.mul_add])))
```

使用本章描述的各种小工具——``match``语句、匿名构造子和``rewrite``策略，我们可以简洁地写出如下证明：

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

就像构造主义的“或”比古典的“或”强，同样，构造的“存在”也比古典的“存在”强。例如，下面的推论需要经典推理，因为从构造的角度来看，知道并不是每一个``x``都满足``¬ p``，并不等于有一个特定的``x``满足``p``。

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x :=  ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

下面是一些涉及存在量词的常见等式。在下面的练习中，我们鼓励你尽可能多写出证明。你需要判断哪些是非构造主义的，因此需要一些经典推理。

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

注意，第二个例子和最后两个例子要求假设至少有一个类型为``α``的元素``a``。

以下是两个比较困难的问题的解：

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from  hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

更多证明语言
--------------------------

我们已经看到像``fun``、``have``和``show``这样的关键字使得写出反映非正式数学证明结构的正式证明项成为可能。在本节中，我们将讨论证明语言的一些通常很方便的附加特性。

首先，我们可以使用匿名的``have``表达式来引入一个辅助目标，而不需要标注它。我们可以使用关键字``this``'来引用最后一个以这种方式引入的表达式:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

通常证明从一个事实转移到另一个事实，所以这可以有效地消除杂乱的大量标签。

当目标可以推断出来时，我们也可以让Lean写``by assumption``来填写证明：

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

这告诉Lean使用``assumption``策略，反过来，通过在局部上下文中找到合适的假设来证明目标。我们将在下一章学习更多关于``assumption``策略的内容。

我们也可以通过写``‹p›``的形式要求Lean填写证明，其中``p``是我们希望Lean在上下文中找到的证明命题。你可以分别使用``\f<``和``\f>``输入这些角引号。字母“f”表示“French”，因为unicode符号也可以用作法语引号。事实上，这个符号在Lean中定义如下:

```lean
notation "‹" p "›" => show p by assumption
```

这种方法比使用``by assumption``更稳健，因为需要推断的假设类型是显式给出的。它还使证明更具可读性。这里有一个更详细的例子:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

你可以这样使用法语引号来指代上下文中的“任何东西”，而不仅仅是匿名引入的东西。它的使用也不局限于命题，尽管将它用于数据有点奇怪：

```lean
example (n : Nat) : Nat := ‹Nat›
```

稍后，我们将展示如何使用Lean中的宏系统扩展证明语言。

练习
---------

1. 证明以下等式：

```lean
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```
你还应该想想为什么在最后一个例子中反过来是不能证明的。

2. 当一个公式的组成部分不依赖于被全称的变量时，通常可以把它提取出一个全称量词的范围。尝试证明这些(第二个命题中的一个方向需要经典逻辑)：

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. 考虑“理发师悖论”：在一个小镇里，这里有一个（男性）理发师给所有不为自己刮胡子的人刮胡子。证明这里存在矛盾：

```lean
variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := sorry
```

4. 如果没有任何参数，类型``Prop``的表达式只是一个断言。填入下面``prime``和``Fermat_prime``的定义，并构造每个给定的断言。例如，通过断言每个自然数``n``都有一个大于``n``的质数，你可以说有无限多个质数。哥德巴赫弱猜想指出，每一个大于5的奇数都是三个素数的和。如果有必要，请查阅费马素数的定义或其他任何资料。

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

5. 尽可能多地证明存在量词一节列出的等式。