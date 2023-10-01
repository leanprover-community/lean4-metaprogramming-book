/-
# Expressions

Expressions (terms of type `Expr`) are an abstract syntax tree for Lean
programs. This means that each term which can be written in Lean has a
corresponding `Expr`. For example, the application `f e` is represented by the
expression `Expr.app ⟦f⟧ ⟦e⟧`, where `⟦f⟧` is a representation of `f` and `⟦e⟧`
a representation of `e`. Similarly, the term `Nat` is represented by the
expression ``Expr.const `Nat []``. (The backtick and empty list are discussed
below.)

式（`Expr`型の項）はLeanプログラムの抽象構文木です。
これは、Leanで書かれる各項に対応する`Expr`が存在することを意味します。
たとえば、適用`f e`は式`Expr.app ⟦f⟧ ⟦e⟧`によって表現されます。
ここで、`⟦f⟧`はfの表現であり、`⟦e⟧`はeの表現です。
同様に、項`Nat`は式``Expr.const `Nat []``によって表現されます。
（バッククォートと空のリストについては以下で説明します。）

The ultimate purpose of a Lean tactic block is to generate a term which serves
as a proof of the theorem we want to prove. Thus, the purpose of a tactic is to
produce (part of) an `Expr` of the right type. Much metaprogramming therefore
comes down to manipulating expressions: constructing new ones and taking apart
existing ones.

Leanのタクティクブロックの最終的な目的は、我々が証明したい定理の証明として機能する項を生成することです。
したがって、タクティクの目的は、適切な型の`Expr`（の一部）を生成することです。
したがって、メタプログラミングの多くは、新しい式の構築と既存の式の分解という形で式の操作に集約されます。

Once a tactic block is finished, the `Expr` is sent to the kernel, which checks
whether it is well-typed and whether it really has the type claimed by the
theorem. As a result, tactic bugs are not fatal: if you make a mistake, the
kernel will ultimately catch it. However, many internal Lean functions also
assume that expressions are well-typed, so you may crash Lean before the
expression ever reaches the kernel. To avoid this, Lean provides many functions
which help with the manipulation of expressions. This chapter and the next
survey the most important ones.

タクティクブロックが終了すると、`Expr`はカーネルに送信され、それが型が正しく、
また、それが宣言された定理によって主張される型を本当に持っているかどうかをチェックします。
結果として、タクティクのバグは致命的ではありません。
間違えても、最終的にはカーネルがそれをキャッチします。
しかし、多くの内部的なLeanの関数も式が型が正しいと仮定しているので、
式がカーネルに到達する前にLeanをクラッシュさせる可能性があります。
これを防ぐために、Leanは式の操作を補助する多くの関数を提供しています。
この章と次の章では、その中で最も重要なものを調査します。

Let's get concrete and look at the
[`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
type:
-/

import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

/-! What is each of these constructors doing?

- `bvar` is a __bound variable__. For example, the `x` in `fun x => x + 2` or
  `∑ x, x²`. This is any occurrence of a variable in an expression where there
  is a binder above it. Why is the argument a `Nat`? This is called a de Bruijn
  index and will be explained later. You can figure out the type of a bound
  variable by looking at its binder, since the binder always has the type
  information for it.

  `bvar`は__束縛変数__です。例えば、`fun x => x + 2`や`∑ x, x²`の`x`のようなものです。
  これは、束縛子が上にある式の中で変数が出現するすぐれたものです。
  なぜ引数は`Nat`なのでしょうか？これはde Bruijnインデックスと呼ばれ、後で説明されます。
  束縛変数の型を知るためには、その束縛子を見ることで判断できます。
  なぜなら、束縛子は常にそれに対する型情報を持っているからです。

- `fvar` is a __free variable__. These are variables which are not bound by a
  binder. An example is `x` in `x + 2`. Note that you can't just look at a free
  variable `x` and tell what its type is, there needs to be a context
  which contains a declaration for `x` and its type. A free variable has an ID
  that tells you where to look for it in a `LocalContext`. In Lean 3, free
  variables were called "local constants" or "locals".

  `fvar`は__自由変数__です。これは束縛子によって束縛されていない変数です。
  例としては、`x + 2`の`x`があります。ただし、自由変数`x`を見てその型をすぐに知ることはできません。
  `x`とその型の宣言を含む文脈が必要です。
  自由変数には、それを`LocalContext`のどこで探すべきかを示すIDがあります。
  Lean 3では、自由変数は"ローカル定数"または"ローカル"と呼ばれていました。

- `mvar` is a __metavariable__. There will be much more on these later, but you
  can think of it as a placeholder or a 'hole' in an expression that needs to be
  filled at a later point.

  `mvar`は__メタ変数__です。これについては後ほど詳しく説明しますが、
  これは表現の中の後で埋める必要のあるプレースホルダーや'穴'と考えることができます。

- `sort` is used for `Type u`, `Prop` etc.
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is a function application. Multiple arguments are done using _partial
  application_: `f x y ↝ app (app f x) y`.

  appは関数の適用です。複数の引数は_部分適用_を使用して行われます：`f x y ↝ app (app f x) y。`

- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`). The `b` argument
  is called the __body__. Note that you have to give the type of the variable
  you are binding.

  `lam n t b`はラムダ式(`fun ($n : $t) => $b`)です。`b`引数は__本体__と呼ばれます。
  変数の型を指定する必要があることに注意してください。

- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`). This is
  also sometimes called a Π-type or Π-expression and is often written `∀ $n :
  $t, $b`. Note that the non-dependent arrow `α → β` is a special case of `(a :
  α) → β` where `β` doesn't depend on `a`. The `E` on the end of `forallE` is to
  distinguish it from the `forall` keyword.

  `forallE n t b`は依存矢印式(`($n : $t) → $b`)です。これは時々Π型またはΠ式と呼ばれ、
  しばしば`∀ $n : $t, $b`と書かれます。
  非依存矢印`α → β`は、`β`が`a`に依存しない場合の`(a : α) → β`の特別な場合です。
  `forallE`の最後の`E`は、`forall`キーワードと区別するためです。

- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or
  `"hello world"`. Literals help with performance: we don't want to represent
  the expression `(10000 : Nat)` as `Nat.succ $ ... $ Nat.succ Nat.zero`.

  `lit`は__リテラル__です。これは`4`や`"hello world"`のような数値や文字列のリテラルです。
  リテラルはパフォーマンスに役立ちます。
  `(10000 : Nat)`という式を`Nat.succ $ ... $ Nat.succ Nat.zero`のように表現したくありません。

- `mdata` is just a way of storing extra information on expressions that might
  be useful, without changing the nature of the expression.

  `mdata`は、式に有用な追加情報を格納する方法であり、式の性質を変えることなく行うことができます。

- `proj` is for projection. Suppose you have a structure such as `p : α × β`,
  rather than storing the projection `π₁ p` as `app π₁ p`, it is expressed as
  `proj Prod 0 p`. This is for efficiency reasons ([todo] find link to docstring
  explaining this).

  `proj`は射影のためです。`p : α × β`のような構造があるとします。
  `app π₁ p`として射影`π₁ p`を格納する代わりに、`proj Prod 0 p`として表現されます。
  これは効率のためです。

You've probably noticed that you can write many Lean programs which do not have
an obvious corresponding `Expr`. For example, what about `match` statements,
`do` blocks or `by` blocks? These constructs, and many more, must indeed first
be translated into expressions. The part of Lean which performs this
(substantial) task is called the elaborator and is discussed in its own chapter.
The benefit of this setup is that once the translation to `Expr` is done, we
have a relatively simple structure to work with. (The downside is that going
back from `Expr` to a high-level Lean program can be challenging.)

おそらく、明確な対応する`Expr`がない多くのLeanプログラムを書くことができることに気付いたことでしょう。
例えば、`match`文や`do`ブロック、`by`ブロックはどうでしょうか？
これらの構造体、そして多くの他のものは、確かに最初に表現に翻訳されなければなりません。
この（大規模な）タスクを実行するLeanの部分はエラボレータと呼ばれ、その章で説明されています。
このセットアップの利点は、Exprへの翻訳が終わったら、私たちは比較的シンプルな構造を操作できるということです。
（デメリットは、`Expr`から高レベルのLeanプログラムに戻るのが難しいことです。）

The elaborator also fills in any implicit or typeclass instance arguments which
you may have omitted from your Lean program. Thus, at the `Expr` level,
constants are always applied to all their arguments, implicit or not. This is
both a blessing (because you get a lot of information which is not obvious from
the source code) and a curse (because when you build an `Expr`, you must supply
any implicit or instance arguments yourself).

エラボレータは、Leanプログラムから省略されている暗黙的な型クラスのインスタンス引数を埋めることもします。
したがって、`Expr`レベルでは、定数は常にすべての引数に適用されます。
これは祝福でもあり（ソースコードから明らかではない多くの情報を得ることができるため）、
呪いでもあります（`Expr`を構築するときに、暗黙的な引数やインスタンス引数を自分で指定する必要があるため）。

## De Bruijn Indexes
ド・ブラウン インデックス

Consider the following lambda expression `(λ f x => f x x) (λ x y => x + y) 5`,
we have to be very careful when we reduce this, because we get a clash in the
variable `x`.

次のラムダ式`(λ f x => f x x) (λ x y => x + y) 5`を考えてみましょう。
この式を簡約するときには、変数`x`で衝突が発生するため、非常に注意する必要があります。

To avoid variable name-clash carnage, `Expr`s use a nifty trick called
__de Bruijn indexes__. In de Bruijn indexing, each variable bound by a `lam` or
a `forallE` is converted into a number `#n`. The number says how many binders up
the `Expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments
for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction. We also
really easily check if two `Expr`s containing bound expressions are equal. This
is why the signature of the `bvar` case is `Nat → Expr` and not
`Name → Expr`.

変数名の衝突を避けるために、`Expr`は__de Bruijnインデックス__と呼ばれる素敵なトリックを使います。
de Bruijnインデックスでは、`lam`または`forallE`によって束縛される各変数が数値`#n`に変換されます。
数値は、この変数を束縛するバインダーを見つけるために`Expr`ツリーを上に何回見るかを示します。
したがって、上記の例は次のようになります（今のところ簡潔さのために型引数にワイルドカード`_`を入れています）。
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
これで、β簡約を実行するときに変数の名前を変更する必要がなくなりました。
また、束縛式を含む2つの`Expr`が等しいかどうかを簡単にチェックできます。
これが、`bvar`ケースのシグネチャが`Nat → Expr`である理由であり、`Name → Expr`ではない理由です。

If a de Bruijn index is too large for the number of binders preceding it, we say
it is a __loose `bvar`__; otherwise we say it is __bound__. For example, in the
expression ``lam `x _ (app #0 #1)`` the `bvar` `#0` is bound by the preceding
binder and `#1` is loose. The fact that Lean calls all de Bruijn indexes `bvar`s
("bound variables") points to an important invariant: outside of some very
low-level functions, Lean expects that expressions do not contain any loose
`bvar`s. Instead, whenever we would be tempted to introduce a loose `bvar`, we
immediately convert it into an `fvar` ("free variable"). Precisely how that
works is discussed in the next chapter.

de Bruijnインデックスが、それに先行するバインダーの数よりも大きい場合、__loose `bvar`__と呼びます。
そうでない場合は、__bound__と呼びます。
たとえば、式``lam `x _ (app #0 #1)``では、`bvar` `#0`は前のバインダーによって束縛され、`#1`はlooseです。
Leanがすべてのde Bruijnインデックスを`bvar`（"bound variables"）と呼ぶという事実は、
重要な不変条件を指しています。
いくつかの非常に低レベルの関数を除いて、Leanは式にloose `bvar`が含まれていないことを期待しています。
代わりに、loose `bvar`を導入しようとするときはいつでも、すぐに`fvar`（"free variable"）に変換します。
それが正確にどのように機能するかは、次の章で説明します。

If there are no loose `bvar`s in an expression, we say that the expression is
__closed__. The process of replacing all instances of a loose `bvar` with an
`Expr` is called __instantiation__. Going the other way is called
__abstraction__.

式にloose `bvar`がない場合、その式を __closed__ と呼びます。
loose `bvar`のすべてのインスタンスを`Expr`で置き換えるプロセスを __instantiation__ と呼びます。
逆の方法は __abstraction__ と呼ばれます。

If you are familiar with the standard terminology around variables, Lean's
terminology may be confusing, so here's a map: Lean's "bvars" are usually called
just "variables"; Lean's "loose" is usually called "free"; and Lean's "fvars"
might be called "local hypotheses".

変数に関する標準的な用語に精通している場合、Leanの用語は混乱する可能性があるため、マップを示します。
Leanの"bvars"は通常、単に"variables"と呼ばれます。
Leanの"loose"は通常"free"と呼ばれ、Leanの"fvars"は"local hypotheses"と呼ばれるかもしれません。

## Universe Levels

Some expressions involve universe levels, represented by the `Lean.Level` type.
A universe level is a natural number, a universe parameter (introduced with a
`universe` declaration), a universe metavariable or the maximum of two
universes. They are relevant for two kinds of expressions.

一部の式には、`Lean.Level`型で表されるuniverse levelsが含まれています。
universe levelは自然数、universe parameter（`universe`宣言で導入される）、
universe metavariable、または2つのuniverseの最大値です。
それらは2種類の式に関連しています。

First, sorts are represented by `Expr.sort u`, where `u` is a `Level`. `Prop` is
`sort Level.zero`; `Type` is `sort (Level.succ Level.zero)`.

最初に、ソートは`Expr.sort u`で表されます。ここで、`u`は`Level`です。
`Prop`は`sort Level.zero`です。`Type`は`sort (Level.succ Level.zero)`です。

Second, universe-polymorphic constants have universe arguments. A
universe-polymorphic constant is one whose type contains universe parameters.
For example, the `List.map` function is universe-polymorphic, as the
`pp.universes` pretty-printing option shows: 

次に、universe-polymorphic constantsにはuniverse argumentsがあります。
universe-polymorphic constantは、その型にuniverse parametersが含まれているものです。
たとえば、`List.map`関数はuniverse-polymorphicです。
`pp.universes`のpretty-printingオプションが示すように： -/

set_option pp.universes true in
#check @List.map

/-!
The `.{u_1,u_2}` suffix after `List.map` means that `List.map` has two universe
arguments, `u_1` and `u_2`. The `.{u_1}` suffix after `List` (which is itself a
universe-polymorphic constant) means that `List` is applied to the universe
argument `u_1`, and similar for `.{u_2}`.

`List.map`の後の`.{u_1,u_2}`のサフィックスは、
`List.map`に2つのuniverse arguments、`u_1`と`u_2`があることを意味します。
`List`の後の`.{u_1}`のサフィックス（それ自体がuniverse-polymorphic constantです）は、
`List`がuniverse argument `u_1`に適用されていることを意味し、`.{u_2}`も同様です。

In fact, whenever you use a universe-polymorphic constant, you must apply it to
the correct universe arguments. This application is represented by the `List Level` 
argument of `Expr.const`. When we write regular Lean code, Lean infers
the universes automatically, so we do not need think about them much. But when
we construct `Expr`s, we must be careful to apply each universe-polymorphic
constant to the right universe arguments.

実際、universe-polymorphic constantを使用するときは、正しいuniverse argumentsに適用する必要があります。
このアプリケーションは、`Expr.const`の`List Level`引数によって表されます。
通常のLeanコードを書くときは、Leanがuniversesを自動的に推論するので、
あまり考える必要はありません。しかし、`Expr`を構築するときは、
各universe-polymorphic constantに正しいuniverse argumentsを適用するように注意する必要があります。

## Constructing Expressions

The simplest expressions we can construct are constants. We use the `const`
constructor and give it a name and a list of universe levels. Most of our
examples only involve non-universe-polymorphic constants, in which case the list
is empty.

構築できる最も単純な式は定数です。`const`コンストラクタを使用し、
名前とuniverse levelsのリストを指定します。
ほとんどの例では、universe-polymorphic constant以外の定数のみを使用します。
その場合、リストは空になります。

We also show a second form where we write the name with double backticks. This
checks that the name in fact refers to a defined constant, which is useful to
avoid typos. 

また、バッククォートを2重にして名前を書く形式も示します。
これにより、名前が実際に定義された定数を参照していることが確認され、
タイプミスを防ぐのに役立ちます。
-/

open Lean

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

/- The double-backtick variant also resolves the given name, making it
fully-qualified. To illustrate this mechanism, here are two further examples.
The first expression, `z₁`, is unsafe: if we use it in a context where the `Nat`
namespace is not open, Lean will complain that there is no constant called
`zero` in the environment. In contrast, the second expression, `z₂`, contains
the fully-qualified name `Nat.zero` and does not have this problem. 

バッククォートを2重にすると、指定された名前が解決され、完全修飾されます。
このメカニズムを説明するために、さらに2つの例を示します。
最初の式`z₁`は安全ではありません。
`Nat`名前空間が開かれていないコンテキストで使用すると、
Leanは環境に`zero`という定数がないとクレームをつけます。
対照的に、2番目の式`z₂`は完全修飾名`Nat.zero`を含んでいるため、この問題はありません。

-/
open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

elab "z₁" : term => return z₁
-- #eval z₁

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

elab "z₂" : term => return z₂
#eval z₂

/- The next class of expressions we consider are function applications. These
can be built using the `app` constructor, with the first argument being an
expression for the function and the second being an expression for the argument.

次に考える式のクラスは、関数適用です。
これらは、最初の引数が関数の式で、2番目の引数が引数の式である`app`コンストラクタを使用して構築できます。

Here are two examples. The first is simply a constant applied to another. The
second is a recursive definition giving an expression as a function of a natural
number. 

2つの例を示します。最初の例は、単に別の定数に適用された定数です。
2番目の例は、自然数の関数として式を与える再帰的な定義です。
-/

def one := Expr.app (.const ``Nat.succ []) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def two := Expr.app (.const ``Nat.succ []) one

def natExpr: Nat → Expr 
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

#eval natExpr 3

/-  Next we use the variant `mkAppN` which allows application with multiple
arguments.

次に、複数の引数を使用したアプリケーションを可能にする`mkAppN`というバリアントを使用します。
 -/

def sumExpr : Nat → Nat → Expr 
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

/- As you may have noticed, we didn't show `#eval` outputs for the two last
functions. That's because the resulting expressions can grow so large that it's
hard to make sense of them.

ご注意の通り、最後の2つの関数の`#eval`出力は示していません。
それは、結果として得られる式が大きくなりすぎて、それらを理解するのが難しいからです。

We next use the constructor `lam` to construct a simple function which takes any
natural number `x` and returns `Nat.zero`. The argument `BinderInfo.default`
says that `x` is an explicit argument (rather than an implicit or typeclass
argument). 

次に、コンストラクタ`lam`を使用して、任意の自然数`x`を取り、`Nat.zero`を返す単純な関数を構築します。
引数`BinderInfo.default`は、`x`が明示的な引数(暗黙の引数や型クラスの引数ではない)であることを示しています。
-/

def constZero : Expr := 
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)

/-! As a more elaborate example which also involves universe levels, here is the
`Expr` that represents `List.map (λ x => Nat.add x 1) []` (broken up into
several definitions to make it somewhat readable):

より詳細な例として、レベルのユニバースも含む、
`List.map (λ x => Nat.add x 1) []`を表す`Expr`を示します(いくつかの定義に分割して、
ある程度読みやすくしています)。
 -/

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

/-! With a little trick (more about which in the Elaboration chapter), we can
turn our `Expr` into a Lean term, which allows us to inspect it more easily. 

少しのトリック(詳細はElaborationの章で説明します)で、
`Expr`をLeanの項に変換することができます。

-/

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{1, 1} Nat Nat (fun x => Nat.add x 1) (@List.nil.{1} Nat) : List.{1} Nat

#reduce mapAddOneNil
-- []

/- In the next chapter we explore the `MetaM` monad, which, among many other
things, allows us to more conveniently construct and destruct larger
expressions.

次の章では、`MetaM`モナドを探索します。
このモナドは、他の多くのことの中で、より便利に大きな式を構築したり分解したりすることを可能にします。

## Exercises
-/
-- 1. Create expression `1 + 2` with `Expr.app`.


def oneAddTwo := 
  Expr.app (Expr.app (.const ``Nat.add []) (natExpr 1)) (natExpr 2)
#eval oneAddTwo

elab "oneAddTwo" : term => return oneAddTwo
#eval oneAddTwo

-- def hoge := Expr.app (natExpr 1) (natExpr 2)
-- elab "hoge" : term => return hoge
-- #eval hoge

-- 2. Create expression `1 + 2` with `Lean.mkAppN`.
def oneAddTwo' := mkAppN (.const ``Nat.add []) #[one, natExpr 2]
#eval oneAddTwo'
elab "oneAddTwo'" : term => return oneAddTwo'
#eval oneAddTwo'

-- 3. Create expression `fun x => 1 + x`.
def addOne' : Expr :=
  .lam `x (.const ``Nat [])
    (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0])
    BinderInfo.default -- BinderInfo.implicitにするとエラーになる
#eval addOne'

elab "addOne'" : term => return addOne'
#eval addOne' 3

-- 4. [**De Bruijn Indexes**] Create expression `fun a, fun b, fun c, (b * a) + c`.
def addMul : Expr :=
  .lam `a nat
    (.lam `b nat
      (.lam `c nat
        (mkAppN (.const ``Nat.add []) #[mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2], .bvar 0])
        BinderInfo.default)
      BinderInfo.default)
    BinderInfo.default
#eval addMul
elab "addMul" : term => return addMul
#eval addMul 2 3 4
#check Exists
-- Forallは定義されていない

-- 5. Create expression `fun x y => x + y`.
def addXY : Expr :=
  .lam `x nat
    (.lam `y nat
      (mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 0])
      BinderInfo.default)
    BinderInfo.default
elab "addXY" : term => return addXY
#eval addXY 2 3

-- 6. Create expression `fun x, String.append "hello, " x`.

def str : Expr := .const ``String []

def addGreetings : Expr :=
  .lam `x str
    (mkAppN (.const ``String.append []) #[mkStrLit "hello, ", .bvar 0])
    BinderInfo.default
elab "addGreetings" : term => return addGreetings
#eval addGreetings "world"

-- 7. Create expression `∀ x : Prop, x ∧ x`.

def prop : Expr := .sort Level.zero

def forallX : Expr :=
  .forallE `x prop 
  (mkAppN (.const ``And []) #[.bvar 0, .bvar 0]) 
  BinderInfo.default

elab "forallX" : term => return forallX
#check forallX

-- 8. Create expression `Nat → String`.
-- def nat : Expr := .const ``Nat [] -- already defined
def natToStr : Expr :=
  .forallE `x nat str BinderInfo.default
  
elab "natToStr" : term => return natToStr
#check natToStr

-- 9. Create expression `fun (p : Prop) => (λ hP : p => hP)`.
def propToProp : Expr :=
  .lam `p prop
    (.lam `hP (.bvar 0) 
      (.bvar 0) 
      .default)
    .default

elab "propToProp" : term => return propToProp
#check propToProp

-- 10. [**Universe levels**] Create expression `Type 6`.
def type6 : Expr := .sort (.ofNat 7)

elab "type6" : term => return type6
#check type6