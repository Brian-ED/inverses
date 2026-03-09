H ← {𝕊w‿x‿n: (w⋈x)⋈×⟜2⌾('a'⊸⋈⁼)n  ;𝕊⁼⟨w‿x⋄n⟩: ⟨w⋄x⋄÷⟜2⌾('a'⊸⋈⁼)n⟩}
F ← {𝕊w‿x‿n: (w⋈x)⋈+⟜2⌾('a'⊸⋈⁼)n  ;𝕊⁼⟨w‿x⋄n⟩: ⟨w⋄x⋄-⟜2⌾('a'⊸⋈⁼)n⟩}
G ← F
# 3 (F G H) 2  {a←0}
{
_Fork ← {
  F‿G‿H _𝕣 x1‿x2‿y1‿y2‿n:
    o1‿n1 ← H x1‿y1‿n
    o2‿n2 ← F x2‿y2‿n1
    G o2‿o1‿n2
  ;F‿G‿H _𝕣⁼ oo‿no:
    o2‿o1‿n2 ← G⁼ oo‿no
    x2‿y2‿n1 ← F⁼ o2‿n2
    x1‿y1‿n ← H⁼ o1‿n1
    x1‿x2‿y1‿y2‿n
}
!3‿3‿2‿2‿⟨'a'⋄0⟩≡F‿G‿H _Fork⁼ F‿G‿H _Fork ⟨3,3,2,2,⟨'a'⋄0⟩⟩
}
{
_Fork ← {
  x1‿x2 F‿G‿H _𝕣 y1‿y2‿n:
    o1‿n1 ← H x1‿y1‿n
    o2‿n2 ← F x2‿y2‿n1
    G o2‿o1‿n2
  ;x1‿x2 F‿G‿H _𝕣⁼ oo‿no:
    o2‿o1‿n2 ← G⁼ oo‿no
    x22‿y2‿n1 ← F⁼ o2‿n2
    x2⁼x22
    x11‿y1‿n ← H⁼ o1‿n1
    x1⁼x11
    y1‿y2‿n
}
!2‿2‿⟨'a'⋄0⟩≡ 3‿3 F‿G‿H _Fork⁼ 3‿3 F‿G‿H _Fork ⟨2,2,⟨'a'⋄0⟩⟩
}

{
_Inv ← {𝕗≡{⋈´}? (!2≡≠)⊸⊢; 𝕗≡{⥊´}? ≢⋈⥊⊣·!2≡≠; 𝔽⁼}
_Fork ← {𝕨F‿G‿H _𝕣 𝕩: a←𝕨F𝕩 ⋄ b←𝕨H𝕩 ⋄ G´a‿b
        ;𝕨F‿G‿H _𝕣⁼𝕩: a‿b←G´_Inv 𝕩  ⋄ o1←𝕨F⁼a ⋄ o2←𝕨H⁼b ⋄ o1⁼o2}
!3‿3≡(-⟜1)‿⥊‿(3‿4⊸∾)_Fork {𝔽⁼𝔽𝕩} 3‿3
!3‿3≡(+⟜1)‿⋈‿⋈_Fork {𝔽⁼𝔽𝕩} 3‿3
}
