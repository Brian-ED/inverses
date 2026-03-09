



eval ← •ReBQN evalDef← {

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

  GenErrorCheckedMona ← {{
     norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼l‿r: norErr≡l? r ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼𝕩: InvChk𝕩? 𝕩≡Op Op⁼𝕩? Op⁼𝕩 ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op⁼𝕩:invErr‿𝕩
    ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op l‿r: invErr≡l? r ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op 𝕩: NorChk𝕩? 𝕩≡Op⁼Op 𝕩? Op 𝕩 ;norErr‿invErr‿NorChk‿InvChk _𝕣_ Op 𝕩:norErr‿𝕩
  }}˙ Mod2 ⋈

  primitives ⇐ ⟨
    ⟨'+' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1‿1≡AreNums¨ ⋄ 1‿1≡AreNums¨⟩ GECD {+} ⟩
    ⟨'-' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1‿1≡AreNums¨ ⋄ 1‿1≡AreNums¨⟩ GECD {-} ⟩
    ⟨'⋈' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ 1 ⋄ {𝕊⟨w⋄a‿b⟩: w≡a; 0} ⟩ GECD {⋈} ⟩
    ⟨'⍟' ⋄ {⇐}‿{⇐} ExtendDyadToMonad ⟨ {⇐} ⋄ {⇐} ⋄ AreNums⊢´ ⋄ 1 ⟩ GECD {{⇐}‿{⇐} ExtendDyadToMonad {⇐}‿{⇐}‿1‿1 GECD {⍟}˙ Mod2 ⋈} ⟩
    ⟨'⁼' ⋄ {{⊢} ≡○•Type 𝕗? 𝔽⁼; ⟨ {⇐} ⋄ {⇐} ⋄ 𝕗⊸≡ ⋄ 1 ⟩ GenErrorCheckedMona {𝕏⁼}𝕗 } ⟩
    ⟨'∘' ⋄ ∘ ⟩
  ⟩
  primitives∾↩⟨
    ⟨'%',"Didn't match"!≡⟩
  ⟩
}

•Show Eval "
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

"
  #(+2)⁼∘((+2)⁼)


#t ← •ReBQN {⇐
#  X←⊢
#  F←{name‿conds⇐𝕩}
#
#  _ExtendDyadToMonad ← {OP _𝕣:
#    errID←{⇐}
#    F←{𝕩⊸OP}
#    F⊘(F⊸{𝕊⁼:𝕎⁼𝕩; 𝕎𝕩})
#  }
#  primitives ⇐ ⟨
#                # InputOutput
#    ⟨'+' ⋄ (F'+'⋈"NN") {g←𝕗 ⋄ {𝕊𝕩: (⟨𝕩⟩⋈g⋈⊢) ; }} ⟩
#    ⟨'-' ⋄ (F'-'⋈"NN") {g←𝕗 ⋄ {𝕊𝕩: (⟨𝕩⟩⋈g⋈⊢) ; }} ⟩
#    ⟨'⋈' ⋄ (F'⋈'⋈"AP") {g←𝕗 ⋄ {𝕊𝕩: (⟨𝕩⟩⋈g⋈⊢) ; }} ⟩
#    ⟨'⍟' ⋄ ! ⟩ # COMPLICATED
#    ⟨'⁼' ⋄ {𝕗} ⟩
#    ⟨'∘' ⋄ {𝕗‿𝕘} ⟩
#    ⟨'%' ⋄ •Show⊢ ⟩
#  ⟩ (⊣⊣ (!⍟≠¬∘∊/⊢)○(⊑¨))evalDef.primitives
#}

#F ← {𝕊(𝕨⋈𝕩)∾⋈} ⋄ D←{1≡•Type𝕩?𝕩; 0≡•Type𝕩? 𝕊¨𝕩; 𝕊{2‿·‿x:x;3‿x‿·‿·:x}•Decompose𝕩} ⋄ D {7𝕏6} {𝕏5} {𝕏4} 3 F {2𝕏1} F 1

## GOAL implement variables somehow as functions assigning to a namespace that's passed around
#•Show T 𝕩
