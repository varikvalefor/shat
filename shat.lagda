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
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
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

\title{le me'oi .Agda.\ velcki be le smimlu be la'o zoi.\ ed(1) .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
  using (
    Main;
    run;
    IO
  )
open import Data.Fin
  using (
    Fin
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
    _$_;
    _∘_
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  using (
    List;
    drop;
    take
  )
open import Data.Maybe
  using (
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  using (
    String
  )
open import Data.Product
  using (
    proj₁;
    Σ
  )
open import System.Environment
  using (
    getArgs
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    length
  )
import Level
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

\newcommand\relsumti[1]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
\item ga jonai ga je da du la'o zoi.\ \IC{Jmina} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei zo'oi .a.\ gi
\item ga jonai ga je da du la'o zoi.\ \IC{Jmini} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ bei zo'oi .i.\ gi
\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
\item ga jonai \relsumti{Vimcu} be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei zo'oi .d.\ gi
\item ga jonai \relsumti{Basti} be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei zo'oi .c.\ gi
\item ga jonai \relsumti{Cusku} be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei zo'oi .p.\ gi
\item \relsumti{Namcusku} be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei zo'oi .n.
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Jmina : BufF x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : BufF x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : BufF x)
        → a Data.Fin.≤ b
        → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
\end{code}

\chapter{le fancu}

\section{la'oi .reed.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ ed(1) .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.\

\begin{code}
reed : (x : Buffer) → String → Maybe $ Cmd x
reed = {!!}
\end{code}

\section{la \F{kanji}.}
ni'o la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ jalge pe'a lo nu co'e la'oi .\B s.\ la'oi .\B x.

\begin{code}
kanji : {x : Buffer} → Cmd x → Maybe $ Buffer ⊎ IO Buffer
kanji = {!!}
\end{code}

\section{la'oi .\F{lupe}.}

\begin{code}
\end{code}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ getArgs IO.>>= uic ∘ Data.List.head
  where
  lupe : (x : Buffer) → IO ⊤
  lupe x = IO.getLine IO.>>= f ∘ reed x
    where
    sin : IO {Level.zero} ⊤
    sin = IO.putStrLn "?"
    f : Maybe $ Cmd x → IO ⊤
    f nothing = IO.putStrLn "?" IO.>> lupe x
    f (just c) with kanji c
    ... | just (inj₁ x') = lupe x'
    ... | just (inj₂ x') = x' IO.>>= lupe
    ... | nothing = lupe x
  uic : Maybe String → IO ⊤
  uic nothing = lupe def
    where
    def = record {
      datnyveicme = nothing;
      lerpinste = "" List.∷ List.[];
      cablerpinsle = Fin.zero
      }
  uic (just c) = {!!} IO.>>= lupe ∘ mkDef
    where
    mkDef = λ t → record {
      datnyveicme = just c;
      lerpinste = Data.String.lines t;
      cablerpinsle = {!!}
      }
\end{code}
\end{document}
