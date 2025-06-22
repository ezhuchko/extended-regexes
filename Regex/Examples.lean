import Regex.MatchingAlgorithm

/-!
# `llmatch` at work

Running examples from the paper, using the `llmatch` function concretely.
-/

open RE BA

def toStringBA (r : BA Char) : String :=
  match r with
  | atom a => a.repr
  | top => "⊤"
  | bot => "⊥"
  | @BA.and _ a b => toStringBA a ++ " ⋓ " ++ toStringBA b
  | @BA.or _ a b => toStringBA a ++ " ⋒ " ++ toStringBA b
  | @BA.not _ a => "¬ " ++ toStringBA a

def toStringRE [ToString A] (r : RE A) : String :=
  match r with
  | ?= r    => "(?= " ++ toStringRE r ++ ")"
  | ?! r    => "(?! " ++ toStringRE r ++ ")"
  | ?<= r   => "(?<=" ++ toStringRE r ++ ")"
  | ?<! r   => "(?<!" ++ toStringRE r ++ ")"
  | ε       => "ε"
  | Pred a  => toString a
  | r1 ⋓ r2 => "(" ++ toStringRE r1 ++ " + " ++ toStringRE r2 ++ ")"
  | r1 ⋒ r2 => "(" ++ toStringRE r1 ++ " & " ++ toStringRE r2 ++ ")"
  | r1 ⬝ r2 => "(" ++ toStringRE r1 ++ "⬝" ++ toStringRE r2 ++ ")"
  | ~ r   => "~" ++ toStringRE r
  | r *     => toStringRE r ++ "*"

instance : ToString (BA Char) where
  toString := toStringBA

instance [ToString A] : ToString (RE A) where
  toString := toStringRE

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

def Rl  : RE (BA Char) := (?<= (Pred $ atom 'a')) ⬝ (Pred $ atom 'b')

-- #eval Option.map Span.match $ llmatch R "0B:1aD2,e".toList
#eval derives ⟨"a".toList,"b".toList,",cde".toList⟩ Rl
-- #eval toStringRE $ der₁ Rl (Span.beg ⟨"a".toList,"b".toList,",cde".toList⟩)
#eval derives₁ ⟨"a".toList,"b".toList,",cde".toList⟩ Rl
def der1 := der₁ Rl (Span.beg ⟨"a".toList,"b".toList,",cde".toList⟩)
def der2 := der₁ der1 (Span.beg ⟨"ba".toList,"".toList,",cde".toList⟩)
#eval toStringRE der2
#eval null₁ der2


def Rlb : RE (BA Char) := (Pred $ atom 'a') ⬝ (?= (Pred $ atom 'a')) ⬝ (Pred $ atom 'a')

#eval derives ⟨"a".toList,"aa".toList,",cde".toList⟩ Rlb
#eval derives₁ ⟨"a".toList,"aa".toList,",cde".toList⟩ Rlb

def der11 := der₁ Rlb (Span.beg ⟨"a".toList,"aa".toList,",cde".toList⟩)
def der22 := der₁ der11 (Span.beg ⟨"aa".toList,"a".toList,",cde".toList⟩)
-- def der33 := der₁ der22 (Span.beg ⟨"aaa".toList,"".toList,",cde".toList⟩) -- does not enter this
#eval toStringRE der22
#eval null₁ der22

#eval derives₁ ⟨":B01".toList,"aD2".toList,",e".toList⟩ R
#eval derives ⟨":B01".toList,"aD2".toList,",e".toList⟩ R

/-- Alternative definitions using negation of regexes
    rather than complementation of character classes -/
def W' := ~ (Pred uc ⋓ Pred lc ⋓ Pred digit)
def R₅ : RE (BA Char) := (?<= W') ⬝ anys ⬝ (?= W')
def R' : RE (BA Char)  := R₁ ⋒ R₂ ⋒ R₃ ⋒ R₅

#eval llmatch R' "0B:1aD2,e".toList

end examples
