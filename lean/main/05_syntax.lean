
/- # Syntax

This chapter is concerned with the means to declare and operate on syntax
in Lean. Since there are a multitude of ways to operate on it, we will
not go into great detail about this yet and postpone quite a bit of this to
later chapters.

この章では、Leanで構文を宣言および操作する手段に焦点を当てています。
それを操作する方法はさまざまなため、詳細には立ち入らず、これについての多くは後の章に先送りします。

## Declaring Syntax

### Declaration helpers

Some readers might be familiar with the `infix` or even the `notation`
commands, for those that are not here is a brief recap:

一部の読者は、`infix`または`notation`コマンドについて知っているかもしれませんが、
そうでない読者のために、ここでは簡単に説明します。
-/

import Lean
import Std
import Std.Classes.SetNotation
import Std.Util.ExtendedBinder

-- XOR, denoted \oplus
infixl:60 " ⊕ " => fun l r => (!l && r) || (l && !r)

#eval true ⊕ true -- false
#eval true ⊕ false -- true
#eval false ⊕ true -- true
#eval false ⊕ false -- false

-- with `notation`, "left XOR"
notation:10 l:10 " LXOR " r:11 => (!l && r)

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false
#eval false LXOR true LXOR false -- false

/- As we can see the `infixl` command allows us to declare a notation for
a binary operation that is infix, meaning that the operator is in between
the operands (as opposed to e.g. before which would be done using the `prefix` command).
The `l` at the end of `infixl` means that the notation is left associative so `a ⊕ b ⊕ c`
gets parsed as `(a ⊕ b) ⊕ c` as opposed to `a ⊕ (b ⊕ c)` (which would be achieved by `infixr`).
On the right hand side, it expects a function that operates on these two parameters
and returns some value. The `notation` command, on the other hand, allows us some more
freedom: we can just "mention" the parameters right in the syntax definition
and operate on them on the right hand side. It gets even better though, we can
in theory create syntax with 0 up to as many parameters as we wish using the
`notation` command, it is hence also often referred to as "mixfix" notation.

見たように、`infixl`コマンドを使用すると、
オペランドの間に演算子がある2項演算の記法を宣言できます（例：前置演算子を使用して行うことができます）。
`infixl`の末尾の`l`は、記法が左結合であることを意味します。
したがって、`a ⊕ b ⊕ c`は、`（a ⊕ b） ⊕ c`として解析されます。
右側では、これらの2つのパラメーターで動作する関数を期待し、いくつかの値を返します。
一方、`notation`コマンドは、より自由度が高く、
構文定義でパラメーターを「言及」するだけで、右側でそれらに操作できます。
しかし、さらに良くなります。理論的には、
`notation`コマンドを使用して0から任意の数のパラメーターまでの構文を作成できます。
したがって、これは「mixfix」記法とも呼ばれます。

The two unintuitive parts about these two are:
- The fact that we are leaving spaces around our operators: " ⊕ ", " LXOR ".
  This is so that, when Lean pretty prints our syntax later on, it also
  uses spaces around the operators, otherwise the syntax would just be presented
  as `l⊕r` as opposed to `l ⊕ r`.
- The `60` and `10` right after the respective commands -- these denote the operator
  precedence, meaning how strong they bind to their arguments, let's see this in action:

これらの2つの直感に反する部分は次のとおりです。
- 演算子の周りにスペースを残していること：「 ⊕ 」、「 LXOR 」。
  これは、後でLeanが構文をきれいに表示するときに、演算子の周りにもスペースを使用するためです。
  そうでなければ、構文は `l⊕r` ではなく `l ⊕ r` として提示されます。
- それぞれのコマンドの直後にある `60` と `10` は、演算子の優先順位を示しています。
  これは、引数にどれだけ強くバインドするかを意味します。これを実行してみましょう。
-/

#eval true ⊕ false LXOR false -- false
#eval (true ⊕ false) LXOR false -- false
#eval true ⊕ (false LXOR false) -- true

/-!
As we can see, the Lean interpreter analyzed the first term without parentheses
like the second instead of the third one. This is because the `⊕` notation
has higher precedence than `LXOR` (`60 > 10` after all) and is thus evaluated before it.
This is also how you might implement rules like `*` being evaluated before `+`.

見たように、Leanインタープリターは、括弧なしで最初の項を解析しました。 
これは、`⊕`記法が`LXOR`（`60 > 10`）よりも高い優先順位を持つためであり、
したがって、それよりも前に評価されるためです。
これは、`+`よりも`*`が評価されるようなルールを実装する方法でもあります。

Lastly at the `notation` example there are also these `:precedence` bindings
at the arguments: `l:10` and `r:11`. This conveys that the left argument must have
precedence at least 10 or greater, and the right argument must have precedence at 11
or greater. The way the arguments are assigned their respective precedence is by looking at
the precedence of the rule that was used to parse them. Consider for example
`a LXOR b LXOR c`. Theoretically speaking this could be parsed in two ways:
1. `(a LXOR b) LXOR c`
2. `a LXOR (b LXOR c)`

最後に、`notation`の例では、引数にも `:precedence` のバインディングがあります。
`l:10` と `r:11`。これは、左側の引数には少なくとも10以上の優先順位が必要であり、
右側の引数には11以上の優先順位が必要であることを示しています。
引数にそれぞれの優先順位を割り当てる方法は、それらを解析するために使用された規則の優先順位を見ることです。
たとえば、`a LXOR b LXOR c`を考えてみましょう。
理論的には、これは2つの方法で解析できます。
1. `(a LXOR b) LXOR c`
2. `a LXOR (b LXOR c)`

Since the arguments in parentheses are parsed by the `LXOR` rule with precedence
10 they will appear as arguments with precedence 10 to the outer `LXOR` rule:
1. `(a LXOR b):10 LXOR c`
2. `a LXOR (b LXOR c):10`

括弧内の引数は、優先順位10の`LXOR`規則によって解析されるため、
外部の`LXOR`規則に優先順位10の引数として表示されます。

However if we check the definition of `LXOR`: `notation:10 l:10 " LXOR " r:11`
we can see that the right hand side argument requires a precedence of at least 11
or greater, thus the second parse is invalid and we remain with: `(a LXOR b) LXOR c`
assuming that:
- `a` has precedence 10 or higher
- `b` has precedence 11 or higher
- `c` has precedence 11 or higher

しかし、`LXOR`の定義を確認すると、右側の引数は少なくとも11以上の優先順位が必要であることがわかります。
したがって、2番目の解析は無効であり、次のようになります。 `(a LXOR b) LXOR c`
- `a`の優先順位は10以上
- `b`の優先順位は11以上
- `c`の優先順位は11以上

Thus `LXOR` is a left associative notation. Can you make it right associative?

したがって、`LXOR`は左結合記法です。右結合記法にできますか？

NOTE: If parameters of a notation are not explicitly given a precedence they will implicitly be tagged with precedence 0.

注意：記法のパラメーターに明示的に優先順位が指定されていない場合、暗黙的に優先順位0が付けられます。

As a last remark for this section: Lean will always attempt to obtain the longest
matching parse possible, this has three important implications.
First a very intuitive one, if we have a right associative operator `^`
and Lean sees something like `a ^ b ^ c`, it will first parse the `a ^ b`
and then attempt to keep parsing (as long as precedence allows it) until
it cannot continue anymore. Hence Lean will parse this expression as `a ^ (b ^ c)`
(as we would expect it to).

このセクションの最後のコメントとして、Leanは常に最も長い一致する解析を取得しようとします。
これには3つの重要な意味があります。
最初に、非常に直感的なもの、右結合演算子 `^` がある場合、
Leanは `a ^ b ^ c` のようなものを見ると、まず `a ^ b` を解析し、
（優先順位が許す限り）解析を続けて、もう続けられなくなるまで解析しようとします。
したがって、Leanはこの式を `a ^ (b ^ c)` として解析します（私たちが期待するように）。

Secondly, if we have a notation where precedence does not allow to figure
out how the expression should be parenthesized, for example:

第二に、式を括弧で囲む方法を優先順位から推測できない記法がある場合、例えば：
-/

notation:65 lhs:65 " ~ " rhs:65 => (lhs - rhs)

/-!
An expression like `a ~ b ~ c` will be parsed as `a ~ (b ~ c)` because
Lean attempts to find the longest parse possible. As a general rule of thumb:
If precedence is ambiguous Lean will default to right associativity.

`a ~ b ~ c` のような式は `a ~ (b ~ c)` として解析されます。
Leanは最も長い解析を見つけようとします。一般的なルールとして：
優先順位が曖昧な場合、Leanは右結合をデフォルトにします。
-/

#eval 5 ~ 3 ~ 3 -- 5 because this is parsed as 5 - (3 - 3)

/-!
Lastly, if we define overlapping notation such as:

最後に、次のような重複する記法を定義すると：
-/

-- define `a ~ b mod rel` to mean that a and b are equivalent with respect to some equivalence relation rel
notation:65 a:65 " ~ " b:65 " mod " rel:65 => rel a b

/-!
Lean will prefer this notation over parsing `a ~ b` as defined above and
then erroring because it doesn't know what to do with `mod` and the
relation argument:

Leanは、上記で定義したように `a ~ b` を解析してからエラーにするよりも、
この記法を優先します。`mod` と関係引数をどうすればよいかわからないためです。
-/

#check 0 ~ 0 mod Eq -- 0 = 0 : Prop

/-!
This is again because it is looking for the longest possible parser which
in this case involves also consuming `mod` and the relation argument.

これは、最も長い可能なパーサーを探しているためです。
この場合、`mod` と関係引数も消費する必要があります。
-/

/-!
### Free form syntax declarations
With the above `infix` and `notation` commands, you can get quite far with
declaring ordinary mathematical syntax already. Lean does however allow you to
introduce arbitrarily complex syntax as well. This is done using two main commands
`syntax` and `declare_syntax_cat`. A `syntax` command allows you add a new
syntax rule to an already existing so-called "syntax category". The most common syntax
categories are:
- `term`, this category will be discussed in detail in the elaboration chapter,
  for now you can think of it as "the syntax of everything that has a value"
- `command`, this is the category for top-level commands like `#check`, `def` etc.
- TODO: ...

上記の `infix` と `notation` コマンドを使用すると、
すでに普通の数学的な構文を宣言することができます。
Leanでは、任意の複雑な構文を導入することもできます。
これは、2つの主要なコマンド `syntax` と `declare_syntax_cat` を使用して行われます。
`syntax` コマンドを使用すると、既存の構文カテゴリに新しい構文規則を追加できます。
最も一般的な構文カテゴリは次のとおりです。
- `term` は、詳細は後の章で説明しますが、
  今のところ「値を持つすべてのものの構文」と考えてください。
- `command` は、`#check`、`def` などのトップレベルコマンドのカテゴリです。

Let's see this in action:
-/

syntax "MyTerm" : term

/-!
We can now write `MyTerm` in place of things like `1 + 1` and it will be
*syntactically* valid, this does not mean the code will compile yet,
it just means that the Lean parser can understand it:

私たちは今、`1 + 1` のようなものの代わりに `MyTerm` を書くことができます。
これは*構文的に*有効であることを意味します。
これは、コードがまだコンパイルされることを意味するものではありません。
これは、Leanパーサーがそれを理解できることを意味します。
-/

def Playground1.test := MyTerm
-- elaboration function for 'termMyTerm' has not been implemented
--   MyTerm

/-!
Implementing this so-called "elaboration function", which will actually
give meaning to this syntax in terms of Lean's fundamental `Expr` type,
is topic of the elaboration chapter.

このように、Leanの基本的な `Expr` 型の意味でこの構文に意味を与える
「展開関数」と呼ばれるものを実装することは、展開の章のトピックです。

The `notation` and `infix` commands are utilities that conveniently bundle syntax declaration
with macro definition (for more on macros, see the macro chapter),
where the contents left of the `=>` declare the syntax.
All the previously mentioned principles from `notation` and `infix` regarding precedence
fully apply to `syntax` as well.

`notation` と `infix` コマンドは、構文宣言とマクロ定義を便利にまとめたものです
（マクロについては、マクロの章を参照してください）。
`=>` の左側の内容は構文を宣言します。
`notation` と `infix` で述べたすべての原則は、`syntax` にも完全に適用されます。

We can, of course, also involve other syntax into our own declarations
in order to build up syntax trees. For example, we could try to build our
own little boolean expression language:

もちろん、構文木を構築するために、
自分の宣言に他の構文を関与させることもできます。
たとえば、独自の小さなブール式言語を構築してみることができます。
-/

namespace Playground2

-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
-- スコープ付き修飾子は、構文宣言がこの `namespace` に残るようにします。
-- なぜなら、この章ではこれを変更し続けるからです。

scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

/-!
While this does work, it allows arbitrary terms to the left and right of our
`AND` and `OR` operation. If we want to write a mini language that only accepts
our boolean language on a syntax level we will have to declare our own
syntax category on top. This is done using the `declare_syntax_cat` command:

これは機能しますが、`AND` と `OR` 操作の左右に任意の項を許可します。
構文レベルでのみブール言語を受け入れるミニ言語を書きたい場合は、
上に独自の構文カテゴリを宣言する必要があります。
これは、`declare_syntax_cat` コマンドを使用して行われます。
-/

declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr

/-!
Now that we are working in our own syntax category, we are completely
disconnected from the rest of the system. And these cannot be used in place of
terms anymore:

これで、独自の構文カテゴリで作業しているので、
システムの残りの部分とは完全に切断されます。
これらはもう項の代わりに使用できません。
-/

#check ⊥ AND ⊤ -- expected term

/-!
In order to integrate our syntax category into the rest of the system we will
have to extend an already existing one with new syntax, in this case we
will re-embed it into the `term` category:

システムの残りの部分に構文カテゴリを統合するには、
既存の構文カテゴリを新しい構文で拡張する必要があります。
この場合、`term` カテゴリに再埋め込みます。
-/

syntax "[Bool|" boolean_expr "]" : term
#check [Bool| ⊥ AND ⊤] -- elaboration function hasn't been implemented but parsing passes

/-!
### Syntax combinators
In order to declare more complex syntax, it is often very desirable to have
some basic operations on syntax already built-in, these include:

より複雑な構文を宣言するには、
構文に基本的な操作が組み込まれていることが望ましい場合があります。
これらには次のものがあります。

- helper parsers without syntax categories (i.e. not extendable)
- alternatives
- repetitive parts
- optional parts

- 構文カテゴリのないヘルパーパーサー（つまり、拡張できない）
- 代替
- 繰り返し部分
- オプションの部分

While all of these do have an encoding based on syntax categories, this
can make things quite ugly at times, so Lean provides an easier way to do all
of these.

これらすべてには、構文カテゴリに基づくエンコーディングがありますが、
これは時にはかなり醜くなる可能性があるため、
Leanはこれらすべてを行うより簡単な方法を提供します。

In order to see all of these in action, we will briefly define a simple
binary expression syntax.
First things first, declaring named parsers that don't belong to a syntax
category is quite similar to ordinary `def`s:

これらすべてを実行するには、
簡単なバイナリ式構文を簡単に定義します。
まず第一に、構文カテゴリに属さない名前付きパーサーを宣言することは、
通常の `def` と非常に似ています。
-/

syntax binOne := "O"
syntax binZero := "Z"

/-!
These named parsers can be used in the same positions as syntax categories
from above, their only difference to them is, that they are not extensible.
That is, they are directly expanded within syntax declarations,
and we cannot define new patterns for them as we would with proper syntax categories.
There does also exist a number of built-in named parsers that are generally useful,
most notably:

これらの名前付きパーサーは、上記の構文カテゴリと同じ位置で使用できます。
それらとの唯一の違いは、拡張できないことです。
つまり、構文宣言内で直接展開され、
適切な構文カテゴリのようにそれらに新しいパターンを定義することはできません。
一般的に便利な組み込みの名前付きパーサーもいくつか存在します。
特に次のものがあります。

- `str` for string literals
- `num` for number literals
- `ident` for identifiers
- ... TODO: better list or link to compiler docs

- 文字列リテラルの `str`
- 数値リテラルの `num`
- 識別子の `ident`

Next up we want to declare a parser that understands digits, a binary digit is
either 0 or 1 so we can write:

次に、数字を理解するパーサーを宣言します。
バイナリデジットは0または1であるため、次のように書くことができます。
-/

syntax binDigit := binZero <|> binOne

/-!
Where the `<|>` operator implements the "accept the left or the right" behaviour.
We can also chain them to achieve parsers that accept arbitrarily many, arbitrarily complex
other ones. Now we will define the concept of a binary number, usually this would be written
as digits directly after each other but we will instead use comma separated ones to showcase
the repetition feature:

`<|>` 演算子は「左または右を受け入れる」動作を実装します。
また、任意の数、任意の複雑さの他のものを受け入れるパーサーを実現するために、
それらをチェーンすることもできます。
次に、バイナリ数の概念を定義します。
通常、これは直接数字の後に書かれますが、
代わりに繰り返し機能を示すためにカンマ区切りの数字を使用します
-/

-- the "+" denotes "one or many", in order to achieve "zero or many" use "*" instead
-- the "," denotes the separator between the `binDigit`s, if left out the default separator is a space

-- 「+」は「1つ以上」を表し、代わりに「0個以上」を実現するには「*」を使用します。
-- 「,」は `binDigit` の区切り文字を表します。省略すると、デフォルトの区切り文字はスペースです。
syntax binNumber := binDigit,+

/-!
Since we can just use named parsers in place of syntax categories, we can now easily
add this to the `term` category:

構文カテゴリの代わりに名前付きパーサーを使用できるため、
これを `term` カテゴリに簡単に追加できます。
-/

syntax "bin(" binNumber ")" : term
#check bin(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check bin() -- fails to parse because `binNumber` is "one or many": expected 'O' or 'Z'

syntax binNumber' := binDigit,* -- note the *
syntax "emptyBin(" binNumber' ")" : term
#check emptyBin() -- elaboration function hasn't been implemented but parsing passes

/-!
Note that nothing is limiting us to only using one syntax combinator per parser,
we could also have written all of this inline:

1つのパーサーに1つの構文コンビネーターしか使用できないという制限はないことに注意してください。
これらすべてをインラインで書くこともできます。
-/

syntax "binCompact(" ("Z" <|> "O"),+ ")" : term
#check binCompact(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
As a final feature, let's add an optional string comment that explains the binary
literal being declared:

最後の機能として、バイナリリテラルを説明するオプションの文字列コメントを追加しましょう。
-/

-- The (...)? syntax means that the part in parentheses is optional
syntax "binDoc(" (str ";")? binNumber ")" : term
#check binDoc(Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes
#check binDoc("mycomment"; Z, O, Z, Z, O) -- elaboration function hasn't been implemented but parsing passes

/-!
## Operating on Syntax
As explained above, we will not go into detail in this chapter on how to teach
Lean about the meaning you want to give your syntax. We will, however, take a look
at how to write functions that operate on it. Like all things in Lean, syntax is
represented by the inductive type `Lean.Syntax`, on which we can operate. It does
contain quite some information, but most of what we are interested in, we can
condense in the following simplified view:

上記で説明したように、この章では、
Leanに構文に与えたい意味を教える方法について詳しく説明しません。
しかし、それに操作を行う関数を書く方法を見てみましょう。
Leanのすべてのものと同様に、構文は
`Lean.Syntax` という帰納型で表されます。
それにはかなりの情報が含まれていますが、
私たちが興味を持っているもののほとんどは、
次の簡略化されたビューにまとめることができます。
-/

namespace Playground2

inductive Syntax where
  | missing : Syntax
  | node (kind : Lean.SyntaxNodeKind) (args : Array Syntax) : Syntax
  | atom : String -> Syntax
  | ident : Lean.Name -> Syntax

end Playground2

/-!
Lets go through the definition one constructor at a time:

定義を1つずつ見ていきましょう。
- `missing` is used when there is something the Lean compiler cannot parse,
  it is what allows Lean to have a syntax error in one part of the file but
  recover from it and try to understand the rest of it. This also means we pretty
  much don't care about this constructor.
- `node` is, as the name suggests, a node in the syntax tree. It has a so called
  `kind : SyntaxNodeKind` where `SyntaxNodeKind` is just a `Lean.Name`. Basically,
  each of our `syntax` declarations receives an automatically generated `SyntaxNodeKind`
  (we can also explicitly specify the name with `syntax (name := foo) ... : cat`) so
  we can tell Lean "this function is responsible for processing this specific syntax construct".
  Furthermore, like all nodes in a tree, it has children, in this case in the form of
  an `Array Syntax`.
- `atom` represents (with the exception of one) every syntax object that is at the bottom of the
  hierarchy. For example, our operators ` ⊕ ` and ` LXOR ` from above will be represented as
  atoms.
- `ident` is the mentioned exception to this rule. The difference between `ident` and `atom`
  is also quite obvious: an identifier has a `Lean.Name` instead of a `String` that represents it.
  Why a `Lean.Name` is not just a `String` is related to a concept called macro hygiene
  that will be discussed in detail in the macro chapter. For now, you can consider them
  basically equivalent.

- `missing` は、Leanコンパイラが解析できないものがあるときに使用されます。
  これにより、Leanはファイルの一部で構文エラーが発生することができますが、
  それから回復して残りの部分を理解しようとします。
  これはまた、私たちがほとんど気にしないことを意味します。
- `node` は、その名前が示すように、構文木のノードです。
  `kind : SyntaxNodeKind` というものがあります。
  `SyntaxNodeKind` は単なる `Lean.Name` です。
  基本的に、`syntax` 宣言のそれぞれに自動生成された `SyntaxNodeKind` があります。
  （`syntax (name := foo) ... : cat` で名前を明示的に指定することもできます）。
  したがって、Leanに「この関数はこの特定の構文構造を処理する責任があります」と伝えることができます。
  さらに、木のノードのように、子にも `Array Syntax` の形であります。
- `atom` は、階層の一番下にあるすべての構文オブジェクトを表します（1つの例外を除く）。たとえば、
  上記の演算子 ` ⊕ ` と ` LXOR ` は、アトムとして表されます。
- `ident` は、このルールの例外としても言及されています。
  `ident` と `atom` の違いも非常に明らかです。
  識別子は、それを表す `Lean.Name` を持っているので、
  `atom` との違いは明らかです。
  `Lean.Name` が `String` ではない理由は、
  マクロの章で詳しく説明するマクロハイジーンと呼ばれる概念に関係しています。
  今のところ、それらは基本的に同等であると考えることができます。
### Constructing new `Syntax`
Now that we know how syntax is represented in Lean, we could of course write programs that
generate all of these inductive trees by hand, which would be incredibly tedious and is something
we most definitely want to avoid. Luckily for us there is quite an extensive API hidden inside the
`Lean.Syntax` namespace we can explore:

Leanで構文がどのように表現されているかを知ったので、
もちろん、これらの帰納的な木を手作業で生成するプログラムを書くことができます。
これは非常に退屈であり、私たちが絶対に避けたいことです。
幸いなことに、私たちには `Lean.Syntax` 名前空間に隠されたかなりの広範なAPIがあります。
これを探索することができます。
-/

open Lean
#check Syntax -- Syntax. autocomplete

/-!
The interesting functions for creating `Syntax` are the `Syntax.mk*` ones that allow us to create
both very basic `Syntax` objects like `ident`s but also more complex ones like `Syntax.mkApp`
which we can use to create the `Syntax` object that would amount to applying the function
from the first argument to the argument list (all given as `Syntax`) in the second one.
Let's see a few examples:

`Syntax` を作成するための興味深い関数は、`Syntax.mk*`です。これにより、
`ident` のような非常に基本的な `Syntax` オブジェクトを作成することもできますが、
`Syntax.mkApp` のようなより複雑なものも作成できます。
これを使用して、第1引数から第2引数の引数リスト（すべて `Syntax` として与えられる）に
関数を適用することになる `Syntax` オブジェクトを作成できます。
いくつかの例を見てみましょう。
-/

-- Name literals are written with this little ` in front of the name
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- is the syntax of `Nat.add 1 1`
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- is the syntax for `1 + 1`

-- note that the `«term_+_» is the auto-generated SyntaxNodeKind for the + syntax

/-
If you don't like this way of creating `Syntax` at all you are not alone.
However, there are a few things involved with the machinery of doing this in
a pretty and correct (the machinery is mostly about the correct part) way
which will be explained in the macro chapter.

もしもこの方法で`Syntax`を作成するのが好きでないのであれば、あなただけではありません。
ただし、これを行うための機械装置には、美しく正確な方法（機械装置のほとんどは正確な部分に関するものです）
がいくつか関与しており、これについてはマクロの章で説明されます。

### Matching on `Syntax`
Just like constructing `Syntax` is an important topic, especially
with macros, matching on syntax is equally (or in fact even more) interesting.
Luckily we don't have to match on the inductive type itself either: we can
instead use so-called "syntax patterns". They are quite simple, their syntax is just
`` `(the syntax I want to match on) ``. Let's see one in action:

`Syntax` を構築することと同様に、特にマクロでは、
syntaxに一致することも同様に（実際にはそれ以上に）興味深いトピックです。
幸いなことに、帰納型自体に一致する必要はありません。
代わりに、いわゆる「構文パターン」を使用できます。
それらは非常にシンプルで、その構文は単に
`` `(一致させたい構文) `` です。
実際に動作するものを見てみましょう。
-/

def isAdd11 : Syntax → Bool
  | `(Nat.add 1 1) => true
  | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false

/-!
The next level with matches is to capture variables from the input instead
of just matching on literals, this is done with a slightly fancier-looking syntax:

次のレベルのマッチは、リテラルに一致するだけでなく、
入力から変数をキャプチャすることです。
これは、少し派手な見た目の構文で行われます。
-/

def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- some ...
#eval isAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo]) -- none

/-!
### Typed Syntax
Note that `x` and `y` in this example are of type `` TSyntax `term ``, not `Syntax`.
Even though we are pattern matching on `Syntax` which, as we can see in the constructors,
is purely composed of types that are not `TSyntax`, so what is going on?
Basically the `` `() `` Syntax is smart enough to figure out the most general
syntax category the syntax we are matching might be coming from (in this case `term`).
It will then use the typed syntax type `TSyntax` which is parameterized
by the `Name` of the syntax category it came from. This is not only more
convenient for the programmer to see what is going on, it also has other
benefits. For Example if we limit the syntax category to just `num`
in the next example Lean will allow us to call `getNat` on the resulting
`` TSyntax `num `` directly without pattern matching or the option to panic:

この例の `x` と `y` は`Syntax`ではなく `` TSyntax `term `` 型であることに注意してください。
コンストラクタで見ることができるように、
`Syntax` にパターンマッチングしているのに、
`TSyntax` ではない型のみで構成されています。
では、何が起こっているのでしょうか？
基本的に、`` `() `` 構文は、
マッチングしている構文が来る可能性のある最も一般的な構文カテゴリ（この場合は `term`）を
推測することができます。
それから、それは構文カテゴリから来た `Name` でパラメータ化された型付き構文型 `TSyntax` を使用します。
これは、プログラマーが何が起こっているかを見るのに便利なだけでなく、
他の利点もあります。
たとえば、次の例では、構文カテゴリを `num` に制限すると、
Leanはパターンマッチングやパニックするオプションなしに、
`` TSyntax `num `` の結果に直接 `getNat` を呼び出すことを許可します。
-/

-- Now we are also explicitly marking the function to operate on term syntax

-- ここでは、関数が項構文で動作するように明示的にマークしています。
def isLitAdd : TSyntax `term → Option Nat
  | `(Nat.add $x:num $y:num) => some (x.getNat + y.getNat)
  | _ => none

#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- some 2
#eval isLitAdd (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- none

/-!
If you want to access the `Syntax` behind a `TSyntax` you can do this using
`TSyntax.raw` although the coercion machinery should just work most of the time.
We will see some further benefits of the `TSyntax` system in the macro chapter.

`TSyntax` の背後にある `Syntax` にアクセスしたい場合は、
`TSyntax.raw` を使用することができます。
ただし、コアション機構はほとんどの場合うまく動作するはずです。
マクロの章で `TSyntax` システムのさらなる利点を見ていきましょう。

One last important note about the matching on syntax: In this basic
form it only works on syntax from the `term` category. If you want to use
it to match on your own syntax categories you will have to use `` `(category| ...)``.

構文に一致することについて最後に重要な注意点があります。
この基本的な形式では、それは `term` カテゴリの構文でのみ機能します。
独自の構文カテゴリに一致させるには、`` `(category| ...)`` を使用する必要があります。

### Mini Project
As a final mini project for this chapter we will declare the syntax of a mini
arithmetic expression language and a function of type `Syntax → Nat` to evaluate
it. We will see more about some of the concepts presented below in future
chapters.

この章の最後のミニプロジェクトとして、
ミニ算術式言語の構文と、それを評価する型 `Syntax → Nat` の関数を宣言します。
以下で説明する概念のいくつかについては、
将来の章で詳しく説明します。
-/

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

-- You can ignore Elab.TermElabM, what is important for us is that it allows
-- us to use the ``(arith| (12 + 3) - 4)` notation to construct `Syntax`
-- instead of only being able to match on it like this.

--- Elab.TermElabM は無視して構いません。
--- 重要なのは、これにより、
--- ``(arith| (12 + 3) - 4)` 構文を構築することができることです。
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  pure (denoteArith stx)

#eval test -- 11

/-!
Feel free to play around with this example and extend it in whatever way
you want to. The next chapters will mostly be about functions that operate
on `Syntax` in some way.

この例を自由に試して、好きなように拡張してください。
次の章では、主に `Syntax` をある種の方法で操作する関数について説明します。
~~~ここまで読んでみるか~~~
-/

/-!
## More elaborate examples
### Using type classes for notations
We can use type classes in order to add notation that is extensible via
the type instead of the syntax system, this is for example how `+`
using the typeclasses `HAdd` and `Add` and other common operators in
Lean are generically defined.

型クラスを使用して、構文システムではなく型を介して拡張可能な表記法を追加することができます。
これは、たとえば`+`が型クラス`HAdd`および`Add`を使用して、
およびLeanの他の一般的な演算子が汎用的に定義されている方法です。

For example, we might want to have a generic notation for subset notation.
The first thing we have to do is define a type class that captures
the function we want to build notation for.

たとえば、部分集合記法の汎用的な記法を持ちたいとします。
最初にやることは、
記法を構築したい関数を捉える型クラスを定義することです。
-/

class Subset (α : Type u) where
  subset : α → α → Prop

/-!
The second step is to define the notation, what we can do here is simply
turn every instance of a `⊆` appearing in the code to a call to `Subset.subset`
because the type class resolution should be able to figure out which `Subset`
instance is referred to. Thus the notation will be a simple:

2番目のステップは、記法を定義することです。
ここでできることは、コードに現れる `⊆` のすべてのインスタンスを `Subset.subset` の呼び出しに変換することです。
なぜなら、型クラスの解決はどの `Subset` インスタンスが参照されているかを推測できるはずだからです。
したがって、記法は単純なものになります。
-/

-- precedence is arbitrary for this example
infix:50 " ⊆ " => Subset.subset

/-!
Let's define a simple theory of sets to test it:

それでは、テストするための単純な集合の理論を定義しましょう。
-/

-- a `Set` is defined by the elements it contains
-- -> a simple predicate on the type of its elements

-- `Set` は、それが含む要素によって定義されます。
-- -> 要素の型に対する単純な述語
def Set (α : Type u) := α → Prop

def Set.mem (x : α) (X : Set α) : Prop := X x

-- Integrate into the already existing typeclass for membership notation

-- 既存のメンバーシップ記法の型クラスに統合する
instance : Membership α (Set α) where
  mem := Set.mem

def Set.empty : Set α := λ _ => False

instance : Subset (Set α) where
  subset X Y := ∀ (x : α), x ∈ X → x ∈ Y

example : ∀ (X : Set α), Set.empty ⊆ X := by
  intro X x
  -- ⊢ x ∈ Set.empty → x ∈ X
  intro h
  exact False.elim h -- empty set has no members

/-!
### Binders
Because declaring syntax that uses variable binders used to be a rather
unintuitive thing to do in Lean 3, we'll take a brief look at how naturally
this can be done in Lean 4.

変数バインダーを使用する構文を宣言することは、
Lean 3ではかなり直感的ではないことでしたので、
Lean 4ではどのように自然に行うことができるかを簡単に見てみましょう。

For this example we will define the well-known notation for the set
that contains all elements `x` such that some property holds:
`{x ∈ ℕ | x < 10}` for example.

この例では、ある性質が成り立つすべての要素 `x` を含む集合のよく知られた記法を定義します。
たとえば、`{x ∈ ℕ | x < 10}` です。

First things first we need to extend the theory of sets from above slightly:

まず最初に、上記の集合の理論を少し拡張する必要があります。
-/

-- the basic "all elements such that" function for the notation

-- 記法のための基本的な「すべての要素」関数
def setOf {α : Type} (p : α → Prop) : Set α := p

/-!
Equipped with this function, we can now attempt to intuitively define a
basic version of our notation:

この関数を備えているので、
記法の基本的なバージョンを直感的に定義することができます。
-/
notation "{ " x " | " p " }" => setOf (fun x => p)

#check { (x : Nat) | x ≤ 1 } -- { x | x ≤ 1 } : Set Nat

example : 1 ∈ { (y : Nat) | y ≤ 1 } := by simp[Membership.mem, Set.mem, setOf]
example : 2 ∈ { (y : Nat) | y ≤ 3 ∧ 1 ≤ y } := by simp[Membership.mem, Set.mem, setOf]

/-!
This intuitive notation will indeed deal with what we could throw at
it in the way we would expect it.

この直感的な記法は、私たちが期待するように、
私たちが投げかけることができるものを扱うでしょう。

As to how one might extend this notation to allow more set-theoretic
things such as `{x ∈ X | p x}` and leave out the parentheses around
the bound variables, we refer the reader to the macro chapter.

この記法を拡張して、
`{x ∈ X | p x}` のようなより集合論的なものを許可し、
バインド変数の周りの括弧を省略する方法については、
マクロの章を参照してください。


## Exercises

1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.

**a)** Using `notation` command.  
**b)** Using `infix` command.  
**c)** Using `syntax` command.  
-/

-- notation:75 l:75 " 💀 " r:85 => l - r
-- #eval 5 * 8 💀 4
-- #eval 8 💀 6 💀 1

-- infixr:75 " 💀 " => fun l r => HSub.hSub l r
set_option quotPrecheck false in
infixr:75 " 💀 " => fun l r => l - r
#eval 5 * 8 💀 4
#eval 8 💀 6 💀 1



/-

Hint: multiplication in Lean 4 is defined as `infixl:70 " * " => HMul.hMul`.

2. Consider the following syntax categories: `term`, `command`, `tactic`; 
and 3 syntax rules given below. Make use of each of these newly defined syntaxes.

```
  syntax "good morning" : term
  syntax "hello" : command
  syntax "yellow" : tactic
```

-/
syntax "good morning" : term
syntax "hello" : command
syntax "yellow" : tactic

def morning_greeting := good morning
hello 
example : True := by
  yellow

/-

3. Create a `syntax` rule that would accept the following commands:

- `red red red 4`
- `blue 7`
- `blue blue blue blue blue 18`

(So, either all `red`s followed by a number; or all `blue`s followed by a number; `red blue blue 5` - shouldn't work.)

Use the following code template:

```
syntax (name := colors) ...
-- our "elaboration function" that infuses syntax with semantics
@[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
```
-/

open Lean Elab Command Term

syntax (name := colors) ("red" <|> "blue")+ num : command
-- our "elaboration function" that infuses syntax with semantics
@[command_elab colors]def elabColors : CommandElab := fun stx => Lean.logInfo "success!"

red red red 4
blue 7
blue red 7

/-

4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.

Create a `syntax` rule that would accept the following commands:

- `#better_help option`
- `#better_help option pp.r`
- `#better_help option some.other.name`

Use the following template:

```
syntax (name := help) ...
-- our "elaboration function" that infuses syntax with semantics
@[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"
```

-/

syntax (name := help) "#better_help" "option" (ident)? : command
-- our "elaboration function" that infuses syntax with semantics
@[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"

#better_help option
#better_help option pp.r
#better_help option some.other.name
/-

5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:

- `∑ x in { 1, 2, 3 }, x^2`
- `∑ x in { "apple", "banana", "cherry" }, x.length`

Use the following template:

```
import Std.Classes.SetNotation
import Std.Util.ExtendedBinder
syntax (name := bigsumin) ...
-- our "elaboration function" that infuses syntax with semantics
@[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666
```

Hint: use the `Std.ExtendedBinder.extBinder` parser.
Hint: you need Std4 installed in your Lean project for these imports to work.

-/
syntax (name := bigsumin) "∑" Std.ExtendedBinder.extBinder " in " "{ " term,* " }, " term : term
-- our "elaboration function" that infuses syntax with semantics
@[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666

#check ∑ x in { 1, 2, 3 }, x^2
#check ∑ x in { "apple", "banana", "cherry" }, x.length