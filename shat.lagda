\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\title{le me'oi .Agda.\ velcki be la'o zoi.\ shat(1) .zoi.\ noi ke'a smimlu la'o zoi.\ ed(1) .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --overlapping-instances #-}

open import IO
  using (
    Main;
    run;
    IO
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    typeOf;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
open import IO.Finite
  using (
    readFile
  )
open import Data.Bool
  using (
    if_then_else_
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    drop;
    take;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    decToMaybe;
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  using (
    unlines;
    String;
    lines
  )
open import Data.Product
  using (
    uncurry;
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃;
    Σ
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no
  )
open import System.Environment
  using (
    getArgs
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    length;
    _++_;
    _∉_;
    cev;
    vec
  )
open import Truthbrary.Category.Monad
  using (
    _>>=_
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

import Level
import Data.Nat.Show
  as ℕ
  using (
    readMaybe;
    show
  )
import Data.Fin.Properties
  as DFP
import Data.Maybe.Instances
\end{code}

\chapter{le se ctaipe}

\section{la'oi .\AgdaRecord{Buffer}.}
ni'o zabna ciksi la'oi .\AgdaRecord{Buffer}.\ fo ma bau la .lojban.

\begin{code}
record Buffer : Set
  where
  field
    datnyveicme : Maybe String
    lerpinste : List String
    cablerpinsle : Fin $ length lerpinste
\end{code}

\section{la'oi .\F{BufF}.}
ni'o zabna ciksi la'oi .\AgdaRecord{Buffer}.\ fo ma bau la .lojban.

\begin{code}
BufF : Buffer → Set
BufF = Fin ∘ length ∘ Buffer.lerpinste
\end{code}

\section{la'oi .\D{Cmd}.}
ni'o ctaipe ko'a goi la'o zoi.\ \D{Cmd} \B x\ .zoi.\ fa lo co'e be lo midnoi be fo la'o zoi.\ ed(1) .zoi.\ ja zo'e be'o poi ctaipe lo su'u tu'a ke'a racli

\newcommand\relsumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei lo sinxa be #2}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
\item ga jonai ga je da du la'o zoi.\ \IC{Jmina} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei zo'oi .a.\ gi
\item ga jonai ga je da du la'o zoi.\ \IC{Jmini} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ bei zo'oi .i.\ gi
\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
\item ga jonai \relsumti{Vimcu}{zo'oi .d.} gi
\item ga jonai \relsumti{Basti}{zo'oi .c.} gi
\item ga jonai \relsumti{Cusku}{zo'oi .p.} gi
\item \relsumti{Namcusku}{zo'oi .n.}
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Jmina : BufF x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : BufF x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : BufF x) → a 𝔽.≤ b → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
\end{code}

\chapter{le fancu}

\section{la'oi .\F{orsygenturfa'i}.}
ni'o ro da poi ke'a ctaipe ko'a goi la'o zoi.\ \F{BufF} \B x\ .zoi.\ zo'u ro de poi ke'a ctaipe ko'a zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{orsygenturfa'i} \B x\ \B s\ .zoi.\ gi ga je da dubjavme'a de gi ga je ko'a me'oi .\IC{just}.\ lo .orsi be li ci bei da bei de bei lo ctaipe be lo su'u da dubjavme'a de gi la'o zoi.\ \B s.\ .zoi.\ konkatena lo sinxa be da lo me'oi .comma.\ lo sinxa be de

\begin{code}
orsygenturfa'i : (x : Buffer)
               → String
               → Maybe $ Σ (BufF x × BufF x) $ uncurry 𝔽._≤_
orsygenturfa'i x = pork ∘ 𝕃.map ps ∘ spit
  where
  spit = splitOn ⦃ {!!} ⦄ ',' ∘ cev ∘ vec
  ps = (_>>= toBufF) ∘ ℕ.readMaybe 10 ∘ cev ∘ vec
    where
    toBufF = Data.Maybe.map 𝔽.fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
  pork : List $ Maybe $ BufF x
       → Maybe $ Σ (BufF x × BufF x) $ uncurry 𝔽._≤_
  pork (just a ∷ just b ∷ []) with a 𝔽.≤? b
  ... | yes x = just $ _ , x
  ... | no _ = nothing
  pork _ = nothing
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i}.\ mapti}

\begin{code}
module Orsygenturfa'iVeritas where
  pav : (x : Buffer)
      → (a b : BufF x)
      → (djb : a 𝔽.≤ b)
      → let showF = ℕ.show ∘ 𝔽.toℕ in
        (_≡_
          (just $ (a , b) , djb)
          (orsygenturfa'i x $ showF a ++ "," ++ showF b))
  pav = {!!}
\end{code}

\section{la'oi .\F{reed}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ ed(1) .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.\

\begin{code}
reed : (x : Buffer) → String → Maybe $ Cmd x
reed = {!!}
\end{code}

\section{la \F{kanji}}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ gi ga je tu'a la'oi .\B s.\ racli gi ko'a me'oi .\IC{just}.\ lo .orsi be li re bei lo jalge be lo nu co'e la'oi .\B s.\ la'oi .\B x.\ be'o bei zo'e poi ga jonai ke'a du la'oi .\IC{nothing}.\ gi ke'a me'oi .\IC{just}.\ zo'e poi cadga fa lo nu cusku ke'a fo lo co'e co mu'oi glibau.\ standard output .glibau.

\begin{code}
kanji : {x : Buffer}
      → Cmd x
      → Maybe $ Buffer × Maybe String
kanji {x} (Cusku a b _) = just $ x ,_ $ just $ cmap i
  where
  BL = Buffer.lerpinste x
  cmap = Data.String.concat ∘ 𝕃.map (𝕃.lookup BL)
  i = 𝕃.filter (a 𝔽.≤?_) $ 𝕃.map Fintoℕ $ 𝕃.allFin $ 𝔽.toℕ b
    where
    Fintoℕ : {n : ℕ}
           → {x : Fin n}
           → Fin $ 𝔽.toℕ x
           → Fin n
    Fintoℕ f = 𝔽.inject≤ f $ DFP.toℕ≤n _
kanji {x} (Namcusku a b m) = Data.Maybe.map (_,_ x ∘ just ∘ viiet) kot
  where
  kot = kanji {x} (Cusku a b m) >>= proj₂
  viiet = unlines ∘ 𝕃.map stringCat' ∘ uin ∘ lines
    where
    stringCat' = λ (x , z) → ℕ.show x ++ "\t" ++ z
    uin : List String → List $ ℕ × String
    uin = 𝕃.zip $ 𝕃.drop (𝔽.toℕ a) $ 𝕃.upTo $ 𝔽.toℕ b
kanji {x} (Vimcu a b _) = just $ x' , nothing
  where
  x' = record x {
    cablerpinsle = {!!};
    lerpinste = 𝕃.map proj₂ $ 𝕃.filter nin $ indice Lz}
    where
    Lz = Buffer.lerpinste x
    indice = λ x → 𝕃.zip (𝕃.allFin $ 𝕃.length x) x
    nin : (x : _)
        → let finek = record {_≟_ = 𝔽._≟_} in
          (Dec $ _∉_ ⦃ Truthbrary.Record.LLC.liliList ⦄ ⦃ finek ⦄
            (proj₁ x)
            (𝕃.map
              (flip 𝔽.inject≤ $ DFP.toℕ≤n _)
              (𝕃.drop (𝔽.toℕ a) $ 𝕃.allFin $ 𝔽.toℕ b)))
    nin _ = _ ≟ _
kanji = {!!}
\end{code}

\subsection{le ctaipe be le su'u la \F{kanji}\ cu mapti}

\begin{code}
module KanjyVeritas where
  dub₂ : (x : Buffer)
       → (c : Cmd x)
       → (Σ
           (Σ (BufF x × BufF x) $ uncurry 𝔽._≤_)
           (λ ((x , z) , d) →
             c ≡ Cusku x z d ⊎ c ≡ Vimcu x z d))
       → just x ≡ Data.Maybe.map proj₁ (kanji c)
  dub₂ _ _ (_ , inj₁ _≡_.refl) = _≡_.refl
  dub₂ _ _ (_ , inj₂ _≡_.refl) = {!!}

  pindices : (x : Buffer)
           → (a b : _)
           → (d : _)
           → let K = kanji {x} $ Cusku a b d in
             let L = K >>= (Data.Maybe.map lines ∘ proj₂) in
             (_≡_
               (L >>= 𝕃.head)
               (just $ 𝕃.lookup (Buffer.lerpinste x) a))
           × (_≡_
               (L >>= 𝕃.head)
               (just $ 𝕃.lookup (Buffer.lerpinste x) b))
  pindices = {!!}
\end{code}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ getArgs IO.>>= uic ∘ 𝕃.head
  where
  uic : Maybe String → IO ⊤
  uic c = maybe mkDef def c IO.>>= lupe
    where
    def = IO.pure record {
      datnyveicme = nothing;
      lerpinste = "" ∷ List.[];
      cablerpinsle = 𝔽.zero
      }
    mkDef : _
    mkDef c = uit IO.<$> readFile c
      where
      uit = λ t → record {
        datnyveicme = just c;
        lerpinste = Data.String.lines t;
        cablerpinsle = {!!}
        }
    lupe : (x : Buffer) → IO ⊤
    lupe x = IO.getLine IO.>>= f ∘ reed x
      where
      sin : ∀ {a} → IO {a} ⊤
      sin = IO.putStrLn "?"
      f : Maybe $ Cmd x → IO ⊤
      f nothing = IO.putStrLn "?" IO.>> lupe x
      f (just c) with kanji c
      ... | nothing = lupe x
      ... | just (x' , nothing) = lupe x'
      ... | just (x' , just z ) = IO.putStrLn z IO.>> lupe x'
\end{code}
\end{document}
