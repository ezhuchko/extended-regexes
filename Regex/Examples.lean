import Regex.MatchingAlgorithm

/-!
# `llmatch` at work

Running examples from the paper, using the `llmatch` function concretely.
-/

open RE
open BA

section examples

/-- Test examples to ensure that matching works in both matching and non-matching cases. -/

def testString1 := "atessdasdtesttestimfdftestpptesttesttestpp".toList
def test1 := "abab".toList

#eval llmatch ((Alternation ("a" : RE (BA Char)) ("ab": RE (BA Char))) * : RE (BA Char)) test1
#eval llmatch ("test" : RE (BA Char)) testString1
#eval llmatch ("test" ⬝ "test" * : RE (BA Char)) testString1
#eval llmatch ("test" * : RE (BA Char)) testString1
#eval llmatch ("ts" ⬝ "ts" * : RE (BA Char)) testString1
#eval "0123456789".characterClass

/-- Main examples from the paper -/

def uc : BA Char := "ABCDEFGHIJKLMOPQRSTUVWXYZ".characterClass
def lc : BA Char := "abcdefghijklmopqrstuvwxyz".characterClass
def digit : BA Char := "0123456789".characterClass
def anys : RE (BA Char) := (Pred ⊤) *
def W := (uc ⊔ lc ⊔ digit)ᶜ

-- (.*[A-Z].*)
def R₁ : RE (BA Char) := anys ⬝ Pred uc ⬝ anys
-- (.*\d.*\d.*)
def R₂ : RE (BA Char) := anys ⬝ Pred digit ⬝ anys ⬝ Pred digit ⬝ anys
-- (.*[a-z].*)
def R₃ : RE (BA Char) := anys ⬝ Pred lc ⬝ anys
-- ((?<=\W).*(?=\W))
def R₄ : RE (BA Char) := (?<= (Pred W)) ⬝ anys ⬝ (?= (Pred W))

def R : RE (BA Char)  := R₁ ⋒ R₂ ⋒ R₃ ⋒ R₄

#eval Option.map Span.match $ llmatch R "0B:1aD2,e".toList
#eval derives ⟨":B0".toList,"1aD2".toList,",e".toList⟩ R
#eval derives ⟨":B01".toList,"aD2".toList,",e".toList⟩ R

/-- Alternative definitions using negation of regexes
    rather than complementation of character classes -/
def W' := ~ (Pred uc ⋓ Pred lc ⋓ Pred digit)
def R₅ : RE (BA Char) := (?<= W') ⬝ anys ⬝ (?= W')
def R' : RE (BA Char)  := R₁ ⋒ R₂ ⋒ R₃ ⋒ R₅

#eval llmatch R' "0B:1aD2,e".toList

end examples
