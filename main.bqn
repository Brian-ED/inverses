



evalDef ⇐ {

  # GenErrorCheckedDyadAsModifier
  gECDAM_ ← {
    _GECDAM_ ← {norErr‿invErr‿NorChk‿InvChk _𝕣_ Op:
      {
       𝕨𝕊⁼l‿⟨r⋄v⟩: norErr≡l? 𝕨≡r? v ;𝕨𝕊⁼𝕩: InvChk𝕨‿𝕩? 𝕩≡𝕨Op 𝕨Op⁼𝕩? 𝕨Op⁼𝕩 ;𝕨𝕊⁼𝕩:invErr⋈𝕨‿𝕩
      ;𝕨𝕊 l‿⟨r⋄v⟩: invErr≡l? 𝕨≡r? v ;𝕨𝕊 𝕩: NorChk𝕨‿𝕩? 𝕩≡𝕨Op⁼𝕨Op 𝕩? 𝕨Op 𝕩 ;𝕨𝕊 𝕩:norErr⋈𝕨‿𝕩
      }
    }
    {𝕨𝔽_𝕣_𝔾𝕩:
      𝕨𝔽_GECDAM_𝔾𝕩
    ;𝕨𝔽_𝕣_𝔾⁼𝕩:
      𝕨𝔽_GECDAM_𝔾⁼𝕩
    }
  }

  Mod2 ← ⟨
    {⇐} ⋄ {⇐}
    {𝕊⟨w⋄x‿y⟩: {◶}≡○•Type w? {!"Temp INTERNAL ERROR: Mod2 couldn't apply non-composing modifier: "∾•Fmt𝕩}⍟¬⊸⊢ 5≡⊑•Decompose {x _w_ y}; 0}
    {𝕊w‿x: 5≡⊑deC←•Decompose x? ·‿b‿c‿d←deC ⋄ w≡c; 0}
  ⟩ _GECDAM_ {w𝕊x‿y: x _w_ y; 𝕊⁼: 5‿𝕨⋈⁼0‿1‿0‿1⊔•Decompose 𝕩}
  Mod1 ← ⟨{⇐}⋄{⇐}⋄ 1⋄1⟩ _GECDAM_ {w𝕊𝕩:𝕩_w; 𝕨𝕊⁼𝕩:⋈⁼4‿𝕨⋈⁼0‿1‿0⊔•Decompose𝕩}
  GECD ← GECDAM_˙ Mod2 ⋈ # GenErrorCheckedDyad

  ggg_ ← {
    _GGG_←{norErrID‿invErrID _𝕣_ g:
      @⟨norErrID⋄invErrID
        1
        {𝕊w‿x:5≡0⊑dd←•Decompose x? g≡3⊑dd; 0}
      ⟩ _GECDAM_ (⊢⟜({⊸}˙ Mod2 {˙}˙⊸Mod1 ⋈ g˙))⊢
    }
    {𝕨𝔽_𝕣_𝔾𝕩:
      𝕨𝔽_GGG_𝔾𝕩
    ;𝕨𝔽_𝕣_𝔾⁼𝕩:
      𝕨𝔽_GGG_𝔾⁼𝕩
    }
  }

  FF ← {𝕊⁼: 𝕎⁼𝕩; 𝕎𝕩}
  ExtendDyadToMonad ← {⊘}˙ Mod2 ·({⊸}˙Mod2 ⋈⟜(ff˙))⌾⊑⌾⌽· ⋈˜ ggg_˙ Mod2 ⋈    ⋄ !{+}≡ ExtendDyadToMonad {id𝔽⁼(id←{⇐}‿{⇐})𝔽𝕩} {+} ⋄ ! 3≡ {4 𝕏⁼ 4 𝕏 3} {⇐}‿{⇐} ExtendDyadToMonad {+}


  AreNums ← {o⊣{o∧↩1≡•Type𝕩}⚇0𝕩⊣o←1}

  GenErrorCheckedMonad ← {{
     norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼l‿r: norErr≡l? r ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼𝕩: InvChk𝕩? 𝕩≡Op Op⁼𝕩? Op⁼𝕩 ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼𝕩:invErr‿𝕩
    ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op l‿r: invErr≡l? r ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op 𝕩: NorChk𝕩? 𝕩≡Op⁼Op 𝕩? Op 𝕩 ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op 𝕩:norErr‿𝕩
  }}˙ Mod2 ⋈

  primitives ⇐ ⟨
    ⟨'+' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1‿1≡AreNums¨ ⋄ 1‿1≡AreNums¨⟩ GECD {+} ⟩
    ⟨'-' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1‿1≡AreNums¨ ⋄ 1‿1≡AreNums¨⟩ GECD {-} ⟩
    ⟨'*' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ (•Type¨0‿0)≡•Type¨ ⋄ 1‿1≡AreNums¨⟩ GECD {{·𝕊𝕩:𝕨Times𝕩; ·𝕊⁼𝕩:𝕨Times⁼𝕩; ·𝕊˜⁼𝕩:𝕨Times˜⁼𝕩}} ⟩
    ⟨'×' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ (•Type¨0‿0)≡•Type¨ ⋄ 1‿1≡AreNums¨⟩ GECD {{·𝕊𝕩:𝕨Times𝕩; ·𝕊⁼𝕩:𝕨Times⁼𝕩; ·𝕊˜⁼𝕩:𝕨Times˜⁼𝕩}} ⟩
    ⟨'⋈' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ {𝕊⟨w⋄a‿b⟩: w≡a; 0} ⟩ GECD {⋈} ⟩
    ⟨'∘' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ 1                  ⟩ GECD {{𝕨𝕊⁼𝕩: 5‿𝕨‿∘⊸∾∘⋈⁼ •Decompose 𝕩 ; 𝕨∘𝕩}}  ⟩
    ⟨'⍟' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ AreNums⊢´ ⋄ 1 ⟩ GECD {{⇐}‿{⇐} ExtendDyadToMonad {⇐}‿{⇐}‿1‿1 GECD {⍟}˙ Mod2 ⋈} ⟩
    ⟨'`' ⋄ {⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ 1 ⟩ GECD {𝕏`}𝕗 } ⟩
    ⟨'⁼' ⋄ {{⊢} ≡○•Type 𝕗? 𝔽⁼; ⟨ {⇐} ⋄ {⇐} ⋄ 𝕗⊸≡ ⋄ 1 ⟩ GenErrorCheckedMonad {𝕏⁼}𝕗 } ⟩
    ⟨'⥊' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ ≡⟜≢´ ⟩ GECD {{𝕊⁼: ⥊𝕩; 𝕨⥊𝕩}} ⟩ # Perfect reshape
    ⟨'/' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ 1 ⟩ GECD {/} ⟩ # Replicate
    ⟨'<' ⋄ ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ 1 ⟩ GenErrorCheckedMonad {⋈} ⟩ # Replicate
    ⟨'↕' ⋄ ⟨ {⇐} ⋄ {⇐} ⋄ AreNums ⋄ {1=≡𝕩? ∧´1=AreNums¨𝕩; 2=≡𝕩? 1∘(↕⁼)⎊0𝕩 ;0} ⟩ GenErrorCheckedMonad {↕} ⟩
    ⟨'⌽' ⋄ ⟨ {⇐} ⋄ {⇐} ⋄ 0<= ⋄ 0<= ⟩ GenErrorCheckedMonad {⌽} ⟩ # Flip
    ⟨'⍉' ⋄ ⟨ {⇐} ⋄ {⇐} ⋄ 0<= ⋄ 0<= ⟩ GenErrorCheckedMonad {⌽} ⟩ # Transpose
    ⟨'⍪' ⋄ ⟨ {⇐} ⋄ {⇐} ⋄ {2≡≠𝕩} ⋄ 1 ⟩ GenErrorCheckedMonad {{𝕊⁼𝕩: 1(⋈⁼∘↑⋈↓)𝕩 ;𝕊𝕩:⋈⊸∾´𝕩}} ⟩
  ⟩
  primitives∾↩⟨
    ⟨'%',"Didn't match"!≡⟩
  ⟩
  repl⇐"loose"
}

Times↩×
#  1‿𝕩 ≡ 0× 𝕩
# ¯1‿𝕩 ≡ 0×⁼𝕩 ≡ 0÷˜𝕩 ≡ 𝕩÷0
# TODO: Oh if a in a‿b is negative then b isn't 0
#{  l‿0𝕊 r‿x:     x {0≡𝕩?𝕨; 𝕩⋈𝕨}  1+l+ r
#      ;  l‿0𝕊⁼r‿x:     x {0≡𝕩?𝕨; 𝕩⋈𝕨} ¯1+l-˜r
#      ;  l‿w𝕊 r‿0:     w {0≡𝕩?𝕨; 𝕩⋈𝕨}  1+l+ r
#      ;  l‿w𝕊⁼r‿0: (  ÷w){0≡𝕩?𝕨; 𝕩⋈𝕨}  1+l-˜r
#      ;  l‿w𝕊 r‿x: (w× x){0≡𝕩?𝕨; 𝕩⋈𝕨}    l+ r
#      ;  l‿w𝕊⁼r‿x: (w÷˜x){0≡𝕩?𝕨; 𝕩⋈𝕨}    l-˜r
#
#      ;  l‿w𝕊 0:   w {0≡𝕩?𝕨; 𝕩⋈𝕨} l+1
#      ;  l‿w𝕊⁼0: (÷w){0≡𝕩?𝕨; 𝕩⋈𝕨} -l
#      ;  w𝕊 0: 1‿w
#      ;  w𝕊⁼0: ¯1⋈÷w
#      ;  0𝕊 r‿x:  x {0≡𝕩?𝕨; 𝕩⋈𝕨} r+1
#      ;  0𝕊⁼r‿x:  x {0≡𝕩?𝕨; 𝕩⋈𝕨} r-1
#      ;  0𝕊 x: 1‿x
#      ;  0𝕊⁼x: ¯1‿x
#      ;  l‿0𝕊 0: {0≡𝕩?𝕨; 𝕩⋈𝕨} l+1
#      ;  l‿0𝕊 x: ?
#      ;  l‿w𝕊 x: l⋈w×x
#      ;  l‿w𝕊⁼x: ?
#      ;  w𝕊 r‿0: ?
#      ;  w𝕊 r‿x: r⋈w×x
#      ;  w𝕊⁼r‿x: ?
#      ;  w𝕊 x: w× x
#      ;  w𝕊⁼x: w÷˜x
#}

[fnNames⋄fns]←⍉>evalDef.primitives

rere ← •ReBQN evalDef

NextLine ← {line𝕊argL:
  (Rere line) {𝔽} argL
}

# Initial tests
Rere "
  2% + +⁼2
  2% +⁼ - -⁼ +2
  2% +⁼ +2
  2% +⁼ +⁼ + +2
  ⟨⟩% + + +⁼ +⁼⟨⟩
  ⟨⟩% +⁼ +⁼ + +⟨⟩

  2% (+2)⁼ 2 + 2
  2% 2+ (+2)⁼ 2

  3% +⁼ 4+⁼ 4+ +3
  ⟨⟩% 4+⁼ 4+ ⟨⟩
  ⟨⟩% + 4+ 4+⁼ +⁼ ⟨⟩
  ⟨⟩% + 4+ 3+⁼ (+3)⁼⁼ 4+⁼ +⁼ ⟨⟩

  0.2% 0.1+⁼ 0.1+ 0.2
  1% 0.014+ 0.362+ 0.312+ 31e130+⁼ 31e130+ 0.312

  ∞% 2+ ∞

  1% 2⋈⁼ ⋈ ⋈⁼ 2⋈ 1
  3% 5⋈⁼ 1+ 4⋈ 2
  2% 5⋈ 5⋈⁼ 2
  2% 3⋈⁼ 2⋈ 2⋈⁼ 3⋈ 2

  {+}% +⁼ + {+}
  2% {+} + {+} +⁼ 2

  2% @ +⁼ +⁼ + @ + 2
  2% {-} + + +⁼ {-} +⁼ 2

  2%{+} ⍟⁼ {+}⍟2

  3%({+}⍟0) ({+}⍟0)⁼ 3
  3%({+}⍟0)⁼ ({+}⍟0)⁼⁼ 3
  9%2({+}⍟3)⁼⁼ 3
  ⟨3⋄3⋈3‿4⟩% 3 ({⋈}⍟3)⁼⁼ 4

  #width=2=1-1 * height=3
  6% 3({+}⍟1)⁼⁼ 3
  ⟨4⋄8⋄12⟩% 3(0+`/)<4

  ⍪2⋈⍪⟨1⋄ ⟨⟩⟩
"

# Encodable and decodable function calls
#F ← {𝕊(𝕨⋈𝕩)∾⋈}
#D←{1≡•Type𝕩?𝕩; 0≡•Type𝕩? 𝕊¨𝕩; 𝕊{2‿·‿x:x;3‿x‿·‿·:x}•Decompose𝕩}
#D {7𝕏6} {𝕏5} {𝕏4} 3 F {2𝕏1} F 1

# Helps me test with non-BQNers
ReRe "
  Plus ← +
  Minus ← -
  Pow ← *
  Mult ← ×
  Pair ← ⋈
  Compose ← ∘
  Power ← ⍟
  _Accumulate ← `
  _Inv ← ⁼
  Reshape ← ⥊
  Replicate ← /
  Enlist ← <
  Range ← ↕
  Flip ← ⌽
  Transpose ← ⍉
  Append ← ⍪
"

•GetLine⊸NextLine∘(⊢⊣·•Out•Fmt)•_while_ 1 Rere •GetLine@
