\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
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
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓰}{\ensuremath{\mathcal g}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl{⌽}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\Xr[2]{\textrm{#1(#2)}}

\title{le me'oi .Agda.\ velcki be la'o zoi.\ \Xr{shat}{1} .zoi.\ noi ke'a smimlu la'o zoi.\ \Xr{ed}{1} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\tableofcontents

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --instance-search-depth=2 #-}

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
    from-inj₁;
    map₁;
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    typeOf;
    _on_;
    _∘₂_;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import IO.Finite
  using (
    readFile
  )
open import Data.Bool
  using (
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    isDigit;
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
  renaming (
    lookup to _!_;
    drop to _↓_;
    take to _↑_
  )
open import Data.Maybe
  using (
    decToMaybe;
    from-just;
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  as 𝕊
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
    ¬_;
    no
  )
open import System.Environment
  using (
    getArgs
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_
  )
open import Truthbrary.Record.SR
  using (
    readMaybe;
    show
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    liliList;
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
  renaming (
    map to mapₘ
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    refl;
    _≡_
  )

import Agda.Builtin.IO
  as ABIO
import Agda.Builtin.Unit
  as ABU
import Data.Fin.Properties
  as DFP
import Data.List.Properties
  as DLP
import Data.Maybe.Instances
import Data.Maybe.Properties
  as DMP
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
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
    citri : List $ Σ (typeOf lerpinste) $ Fin ∘ length
    rejgaudatni : Maybe String
  F = typeOf cablerpinsle
  cninycitri = (lerpinste , cablerpinsle) ∷ citri
\end{code}

\subsection{tu'a la'oi .\D{Fin}.}
ni'o tu'a la'oi .\D{Fin}.\ nibli ko'a goi le su'u ro da poi ke'a ctaipe la'oi .\AgdaRecord{Buffer}.\ zo'u li su'o co'e ja nilzilcmi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be da  .i pilno le co'e co ke na'e me mu'oi zoi.\ \F{if\AgdaUnderscore{}then\AgdaUnderscore{}else\AgdaUnderscore} .zoi.\ ki'u le su'u ko'a milxe ko'e goi le ka ce'u fegli la .varik.\ldots kei je ku'i cu mleca fi ko'e je le ka tu'a ce'u frili kei fe lo jalge be lo nu la'o zoi.\ \AgdaField{Buffer.cablerpinsle} .zoi.\ ctaipe la'o zoi.\ \Sym(\B x \Sym : \AgdaRecord{Buffer}\Sym) \Sym → \F{if} \Sym(\AgdaNumber 0 \OpF{ℕ.≤} \F{length} \Sym(\AgdaField{Buffer.lerpinste} \B x\Sym)\Sym) \Sym(\AgdaField{Buffer.F} \B x\Sym) \D ⊤\ .zoi.

\section{la'oi .\D{Cmd}.}
ni'o ctaipe ko'a goi la'o zoi.\ \D{Cmd} \B x\ .zoi.\ fa lo co'e be lo midnoi be fo la'o zoi.\ \Xr{ed}{1} .zoi.\ ja zo'e be'o poi ctaipe lo su'u tu'a ke'a racli

\newcommand\cibysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei #2}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'oi .\IC{Sisti}.\ gi da mapti zo'oi .q.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!}.\ gi da mapti zo'oi .Q.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Xruti}\ \B z.\ .zoi.\ gi da mapti zo'oi .u.\ldots je ku'i cu mapti le meirmoi be la'oi .\B z.\ bei fo la'o zoi.\ \AgdaField{Buffer.citri} \B x\ .zoi.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Jmina} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei zo'oi .a.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Jmini} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ bei zo'oi .i.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
	\item ga jonai \cibysumti{Vimcu}{zo'oi .d.} gi
	\item ga jonai \cibysumti{Muvgau}{zo'oi .m.} gi
	\item ga jonai \cibysumti{Basti}{zo'oi .c.} gi
	\item ga jonai \cibysumti{Cusku}{zo'oi .p.} gi
	\item \cibysumti{Namcusku}{zo'oi .n.}
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Sisti : Cmd x
  Sisti! : Cmd x
  Jmina : Buffer.F x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : Buffer.F x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : Buffer.F x) → a 𝔽.≤ b → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
  Muvgau : typeOf Vimcu
  Xruti : Fin $ length $ Buffer.citri x → Cmd x
\end{code}

\section{la'oi .\D{Cmdᵢₒ}.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Cmdᵢₒ} \B x\ .zoi.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgauᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka lo nu rejgau benji la'oi .\B a.\ lo datnyvei poi ke'a selcme la'oi .\B b.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Tciduᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka tu'a lo ctaipe be la'oi .\AgdaRecord{Buffer}.\ poi ro de poi ke'a xi pa ctaipe lo me'oi .\F{BufF}.\ be ke'a xi re zo'u ga jonai lo meirmoi be de bei fo ko'e goi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be ke'a cu meirmoi de fo ko'a goi la'o zoi.\ \AgdaField{Buffer.lerpinste} \B x\ .zoi.\ gi ga jonai ga je de zmadu la'oi .\B b.\ je cu dubjavme'a ko'i goi lo nilzilcmi be ko'o goi lo'i ro lerpinsle be lo datnyvei poi ke'a xi re selcme la'oi .\B b.\ gi lo meirmoi be da bei fo ko'e cu meirmoi be lo vujnu be da bei ko'i fo ko'o gi ga je da zmadu la'oi .\B b.\ jenai cu dubjavme'a ko'i gi lo meirmoi be da bei fo ko'e cu meirmoi lo vujnu be da bei la'oi .\B b.\ fo ko'a gi
	\item ga jonai ga je da du la'oi .\IC{Sistiᵢₒ}.\ gi tu'a da rinka lo nu co'e ja kajde ja cu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!ᵢₒ}.\ gi tu'a da rinka lo nu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga je da du la'o zoi.\ \IC{Skamiᵢₒ} \B x\ .zoi.\ gi tu'a da rinka lo nu .uniks.\ co'e la'oi .\B x.
\end{itemize}

\begin{code}
data Cmdᵢₒ (x : Buffer) : Set where
  Rejgauᵢₒ : String → String → Cmdᵢₒ x
  Tciduᵢₒ : String → Buffer.F x → Cmdᵢₒ x
  Skamiᵢₒ : String → Cmdᵢₒ x
  Sistiᵢₒ : Cmdᵢₒ x
  Sisti!ᵢₒ : Cmdᵢₒ x
\end{code}

\chapter{le fancu}

\section{la \F{dekydu'i}}
ni'o xu sarcu fa lo nu la .varik.\ cu ciksi la \F{dekydu'i} bau la .lojban.

\begin{code}
dekydu'i : {x n : ℕ}
         → {m : x ℕ.< n}
         → decToMaybe (x ℕ.<? n) ≡ just m
dekydu'i = {!!}
\end{code}

\section{la'oi .\F{fromℕ?}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{fromℕ?}\ \B x\ .zoi.\ gi la'o zoi.\ \F{mapₘ} \F{𝔽.toℕ} \OpF \$ \F{fromℕ?}\ \B x\ .zoi.\ me'oi .\IC{just}.\ zo'e poi la'oi .\B x.\ mu'oi zoi.\ \F{𝔽.toℕ}\ .zoi.\ ke'a

\begin{code}
fromℕ? : {n : ℕ} → ℕ → Maybe $ Fin n
fromℕ? = mapₘ 𝔽.fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{fromℕ?}.\ mapti}

\begin{code}
module Binxo𝔽?Veritas where
  pav : {n : ℕ}
      → (x : ℕ)
      → x ℕ.< n
      → just x ≡ mapₘ 𝔽.toℕ (fromℕ? {n} x)
  pav {n} x m = sym $ begin
    mapₘ 𝔽.toℕ (fromℕ? {n} x) ≡⟨ refl ⟩
    mapₘ 𝔽.toℕ (mapₘ 𝔽.fromℕ< $ c? x) ≡⟨ mapmapi $ c? x ⟩
    mapₘ id' (c? x) ≡⟨ dekydu'i ▹ cong (mapₘ id') ⟩
    mapₘ id' (just m) ≡⟨ DMP.map-just {f = id'} refl ⟩
    just (id' m) ≡⟨ DFP.toℕ-fromℕ< m ▹ cong just ⟩
    just x ∎
    where
    id' = 𝔽.toℕ ∘ 𝔽.fromℕ<
    c? : (x : ℕ) → Maybe $ x ℕ.< n
    c? = decToMaybe ∘ (ℕ._<? _)
    mapmapi : ∀ {a} → {A B C : Set a}
            → {f : A → B}
            → {g : B → C}
            → (x : Maybe A)
            → mapₘ g (mapₘ f x) ≡ mapₘ (g ∘ f) x
    mapmapi (just _) = refl
    mapmapi nothing = refl
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
\end{code}

\section{la'oi .\F{degjygirzu}.}
ni'o la .varik.\ na birti lo du'u ma kau zabna ciksi la \F{degjygirzu}\ fo mo kau bau la .lojban.

\begin{code}
degjygirzu : String → List String
degjygirzu = 𝕊.wordsBy aintDigit?
  where
  aintDigit? = Data.Bool.T? ∘ Data.Bool.not ∘ isDigit 
\end{code}

\subsection{le ctaipe be le su'u la \F{degjygirzu}\ cu mapti}

\begin{code}
module DegjygirzuVeritas where
  pav : (n : ℕ) → degjygirzu (show n) ≡ show n ∷ []
  pav = {!!}

  rel : (L : List String)
      → (s : String)
      → (t : ℕ)
      → (c : Char)
      → Data.Bool.false ≡ isDigit c
      → (_≡_
          (show t ∷ degjygirzu s)
          (degjygirzu $ show t ++ 𝕊.fromChar c ++ s))
  rel = {!!}
\end{code}

\section{la'oi .\F{pamoinamcu}.}
ni'o ro da xi pa poi ke'a na'e degji lerfu zo'u ro da xi re poi ke'a ctaipe la'oi .\AgdaPostulate{String}.\ zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{pamoinamcu} \B x\ .zoi.\ gi su'o de poi ke'a kacna'u zo'u ga je la'oi .\B x.\ konkatena lo sinxa be de bei de xi pa bei de xi re gi ko'a de me'oi .\IC{just}.

\begin{code}
pamoinamcu : String → Maybe ℕ
pamoinamcu = (_>>= readMaybe) ∘ 𝕃.head ∘ degjygirzu
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{pamoinamcu}.\ mapti}

\begin{code}
module PamoinamcuVeritas where
  non : ((n : ℕ) → readMaybe (show n) ≡ just n)
      → (n : ℕ)
      → just n ≡ pamoinamcu (show n)
  non rimco n = sym $ begin
    pamoinamcu (show n) ≡⟨ refl ⟩
    𝕃.head (s $ show n) >>= readMaybe ≡⟨ refl ⟩
    𝓰 (s $ show n) ≡⟨ DegjygirzuVeritas.pav n ▹ cong 𝓰 ⟩
    𝓰 (show n ∷ []) ≡⟨ refl ⟩
    𝕃.head (show n ∷ []) >>= readMaybe ≡⟨ refl ⟩
    readMaybe (show n) ≡⟨ rimco n ⟩
    just n ∎
    where
    𝓰 = (_>>= readMaybe) ∘ 𝕃.head
    s = 𝕊.wordsBy $ Data.Bool.T? ∘ Data.Bool.not ∘ Data.Char.isDigit
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning

  pav : (n : ℕ)
      → (x : String)
      → (j : Data.Maybe.Is-just $ 𝕊.head x)
      → Data.Bool.false ≡_ $ isDigit $ Data.Maybe.to-witness j
      → just n ≡ pamoinamcu (show n ++ x)
  pav n x j f = sym $ begin
   pamoinamcu (show n ++ x) ≡⟨ refl ⟩
   𝕃.head (s $ show n ++ x) >>= readMaybe ≡⟨ refl ⟩
   𝓰 (s $ show n ++ x) ≡⟨ {!!} ⟩
   𝓰 (s $ show n ++ c' ++ 1↓x) ≡⟨ {!!} ⟩
   𝓰 (show n ∷ s x) ≡⟨ refl ⟩
   readMaybe (show n) ≡⟨ {!!} ⟩
   just n ∎
   where
   c = Data.Maybe.to-witness j
   c' = 𝕊.fromChar c
   𝓰 = (_>>= readMaybe) ∘ 𝕃.head
   s = degjygirzu
   1↓x = 𝕊.fromList $ 1 ↓_ $ 𝕊.toList x
   open import Relation.Binary.PropositionalEquality
   open ≡-Reasoning
\end{code}

\section{la'oi .\F{romoivimcu}.}
ni'o la .varik.\ na birti lo du'u ciksi la'oi .\F{romoivimcu}.\ fo ma kau poi ke'a zabna je cu te gerna la .lojban.

\begin{code}
romoivimcu : String → String
romoivimcu = S $ 𝕃.reverse ∘ _↓_ 1 ∘ 𝕃.reverse
  where
  S = λ f → 𝕊.fromList ∘ f ∘ 𝕊.toList
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{romoivimcu}.\ mapti}

\begin{code}
module RomoivimcuVeritas where
  pav : (x : String)
      → (_≡_
          x
          (_++_
            (romoivimcu x)
            (maybe 𝕊.fromChar "" $ 𝕃.last $ 𝕊.toList x)))
  pav x = sym $ begin
    romoivimcu x ++ r ≡⟨ refl ⟩
    𝕊.fromList (⌽1↓⌽ $ 𝕊.toList x) ++ r ≡⟨ takedrop ⟩
    𝕊.fromList (_↑ x' $ length x' ℕ.∸ 1) ++ r ≡⟨ {!!} ⟩
    𝕊.fromList x'' ≡⟨ x''≡x' ▹ cong 𝕊.fromList ⟩
    𝕊.fromList x' ≡⟨ [cev∘vec]² x ▹ sym ⟩
    x ∎
    where
    ⌽1↓⌽ = 𝕃.reverse ∘ _↓_ 1 ∘ 𝕃.reverse
    r = maybe 𝕊.fromChar "" $ 𝕃.last $ 𝕊.toList x
    x' = 𝕊.toList x
    x'' = _↑_ lx x' ++ _↓_ lx x'
      where
      lx = length x' ℕ.∸ 1
    x''≡x' : x'' ≡ x'
    x''≡x' = DLP.take++drop (length x' ℕ.∸ 1) x'
    [cev∘vec]² : (x : String)
               → x ≡ 𝕊.fromList (𝕊.toList x)
    [cev∘vec]² = {!!}
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
    takedrop = f 1 x' ▹ cong ((𝕊._++ r) ∘ 𝕊.fromList)
      where
      f : ∀ {a} → {A : Set a}
        → (m : ℕ)
        → (x : List A)
        → (_≡_
            (𝕃.reverse $ m ↓ 𝕃.reverse x)
            (_↑_ (𝕃.length x ℕ.∸ m) x))
      f = {!!}
\end{code}

\section{la'oi .\F{orsygenturfa'i}.}
ni'o ro da poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro de poi ke'a ctaipe ko'a zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{orsygenturfa'i} \B s\ .zoi.\ gi ga je da dubjavme'a de gi ga je ko'a me'oi .\IC{just}.\ lo .orsi be li re bei lo .orsi be li re bei da bei de be'o bei lo ctaipe be lo su'u da dubjavme'a de gi la'oi .\B s.\ konkatena lo sinxa be da lo me'oi .comma.\ lo sinxa be de

\begin{code}
module Orsygenturfa'i where
  ps : {n : ℕ} → List Char → Maybe $ Fin n
  ps = (_>>= fromℕ?) ∘ readMaybe ∘ 𝕊.fromList

  spit : String → List $ List Char
  spit = splitOn ⦃ record {_≟_ = Data.Char._≟_} ⦄ ',' ∘ 𝕊.toList

  pork : {n : ℕ}
       → List $ Maybe $ Fin n
       → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  pork (just a ∷ just b ∷ []) = mapₘ (_ ,_) $ decToMaybe $ a 𝔽.≤? b
  pork _ = nothing

  orsygenturfa'i : {n : ℕ}
                 → String
                 → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  orsygenturfa'i = pork ∘ 𝕃.map ps ∘ spit

open Orsygenturfa'i
  using (
    orsygenturfa'i
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{orgenturfa'i}.\ jenai zo'e bau la .lojban.

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i}.\ mapti}

\begin{code}
module Orsygenturfa'iVeritas where
  open Orsygenturfa'i

  spit-du : (x z : String)
          → ',' ∉ 𝕊.toList x
          → ',' ∉ 𝕊.toList z
          → (_≡_
              (spit $ x ++ "," ++ z)
              (𝕊.toList x ∷ 𝕊.toList z ∷ []))
  spit-du = {!!}

  ps-du : {n : ℕ}
        → (x : Fin n)
        → just x ≡ ps (𝕊.toList $ show $ 𝔽.toℕ x)
  ps-du x = sym $ begin
    ps (𝕊.toList $ showF x) ≡⟨ refl ⟩
    b𝔽 (rM $ id' $ showF x) ≡⟨ cvd x ▹ cong (b𝔽 ∘ readMaybe) ⟩
    b𝔽 (rM $ showF x) ≡⟨ rimco (𝔽.toℕ x) ▹ cong b𝔽 ⟩
    b𝔽 (just $ 𝔽.toℕ x) ≡⟨ refl ⟩
    just (𝔽.toℕ x) >>= fromℕ? ≡⟨ refl ⟩
    fromℕ? (𝔽.toℕ x) ≡⟨ refl ⟩
    mapₘ 𝔽.fromℕ< (decToMaybe $ _ ℕ.<? _) ≡⟨ dekydu'is ⟩
    mapₘ 𝔽.fromℕ< (just $ DFP.toℕ<n x) ≡⟨ refl ⟩
    mapₘ 𝔽.fromℕ< _ ≡⟨ DMP.map-just {f = 𝔽.fromℕ<} refl ⟩
    just (𝔽.fromℕ< $ DFP.toℕ<n x) ≡⟨ refl ⟩
    just _ ≡⟨ DFP.fromℕ<-toℕ _ _ ▹ cong just ⟩
    just x ∎
    where
    rM = readMaybe
    b𝔽 = _>>= fromℕ?
    id' = 𝕊.fromList ∘ 𝕊.toList
    showF : {n : ℕ} → Fin n → String
    showF = show ∘ 𝔽.toℕ
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
    dekydu'is = dekydu'i ▹ cong (mapₘ 𝔽.fromℕ<)
    rimco : (n : ℕ) → rM (show n) ≡ just n
    rimco = {!!}
    cvd : {n : ℕ} → (x : Fin n) → id' (showF x) ≡ showF x
    cvd x = istu $ showF x
      where
      istu : (x : String) → id' x ≡ x
      istu = {!!}

  pork-du : {n : ℕ}
          → {x z : Fin n}
          → (djb : x 𝔽.≤ z)
          → (_≡_
              (pork $ just x ∷ just z ∷ [])
              (just $ (x , z) , djb))
  pork-du = {!!}

  pav : {n : ℕ}
      → (a b : Fin n)
      → (djb : a 𝔽.≤ b)
      → let showF = show ∘ 𝔽.toℕ in
        (_≡_
          (just $ (a , b) , djb)
          (orsygenturfa'i $ showF a ++ "," ++ showF b))
  pav a b djb = sym $ begin
    orsygenturfa'i (showF a ++ "," ++ showF b) ≡⟨ refl ⟩
    pork (𝕃.map ps $ spit a,b) ≡⟨ cong pork uimint ⟩
    pork (just a ∷ just b ∷ []) ≡⟨ pork-du djb ⟩
    just ((a , b) , djb) ∎
    where
    showF : {n : ℕ} → Fin n → String
    showF = show ∘ 𝔽.toℕ

    a,b = showF a ++ "," ++ showF b

    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
    -- | ni'o la .varik. na birti lo du'u ma kau zmadu
    -- zo .uimint. fi zo'e ja le ka ce'u .indika... je le
    -- ka ce'u banzuka le ka ce'u xi re cmalu kei lo nu
    -- tu'a ce'u frili cumki
    uimint = begin
      𝕃.map ps (spit a,b) ≡⟨ spidus a b ▹ cong (𝕃.map ps) ⟩
      𝕃.map ps (showF' a ∷ showF' b ∷ []) ≡⟨ refl ⟩
      𝕃.map justF' (a ∷ b ∷ []) ≡⟨ justymapdu $ a ∷ b ∷ [] ⟩
      𝕃.map just (a ∷ b ∷ []) ≡⟨ refl ⟩
      just a ∷  just b ∷ [] ∎
      where
      showF' : {n : ℕ} → Fin n → List Char
      showF' = 𝕊.toList ∘ showF
      justF' : {n : ℕ} → Fin n → Maybe $ Fin n
      justF' = ps ∘ showF'
      justF'≡just : {n : ℕ} → (x : Fin n) → justF' x ≡ just x
      justF'≡just x = sym $ ps-du x
      justymapdu : {n : ℕ}
                 → (L : List $ Fin n)
                 → 𝕃.map justF' L ≡ 𝕃.map just L
      justymapdu = DLP.map-cong justF'≡just
      spidus : {n : ℕ}
             → (a b : Fin n)
             → (_≡_
                 (spit $ showF a ++ "," ++ showF b)
                 (showF' a ∷ showF' b ∷ []))
      spidus a b = spit-du (showF a) (showF b) (nokom a) (nokom b)
        where
        nokom : {n : ℕ}
              → (x : Fin n)
              → ',' ∉ 𝕊.toList (showF x)
        nokom = {!!}
\end{code}

\section{la'oi .\F{reed}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ \Xr{ed}{1} .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.

\begin{code}
module Reed where
  module No where
    g : {x : Buffer} → Char → Maybe $ Cmd x
    g {x} 'w' = mapₘ Rejgau $ Buffer.datnyveicme x
    g 'u' = mapₘ Xruti $ 𝕃.head $ 𝕃.allFin _
    g 'q' = just Sisti
    g 'Q' = just Sisti!
    g _ = nothing

    k : {x : Buffer} → List String → Maybe $ Cmd x
    k ("w" ∷ xs@(_ ∷ _)) = just $ Rejgau $ 𝕊.unwords xs
    k _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t s = _>>= g $ 𝕃.head $ 𝕊.toList s

  module Pa where
    g : {x : Buffer} → Buffer.F x → Char → Maybe $ Cmd x
    g n 'a' = just $ Jmina n
    g n 'i' = just $ Jmini n
    g _ _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = _,ₘ_ n (romoi s) >>= uncurry g
      where
      romoi = 𝕃.last ∘ 𝕊.toList
      n = pamoinamcu s >>= fromℕ?
      _,ₘ_ = (Data.Maybe.ap ∘₂ mapₘ) _,_

  module Re where
    g : (x : Buffer)
      → (a b : Buffer.F x)
      → (a 𝔽.≤ b)
      → Char
      → Maybe $ Cmd x
    g x a b z j with j
    ... | 'c' = just $ Basti a b z
    ... | 'd' = just $ Vimcu a b z
    ... | 'm' = just $ Muvgau a b z
    ... | 'n' = just $ Namcusku a b z
    ... | 'p' = just $ Cusku a b z
    ... | _ = nothing

    t : (x : Buffer) → String → Maybe $ Cmd x
    t x s = _>>= g' $ (Data.Maybe.ap ∘₂ mapₘ) _,_ (romoi s) og
      where
      og = orsygenturfa'i $ romoivimcu s
      romoi = 𝕃.last ∘ 𝕊.toList
      g' = λ (r' , (a , b) , z) → g x a b z r'

  reed : (x : Buffer) → String → Maybe $ Cmd x
  reed x s = 𝕃.head $ 𝕃.mapMaybe id terp
    where
    terp : List $ Maybe $ Cmd x
    terp = No.t s ∷ Pa.t s ∷ Re.t x s ∷ No.k s' ∷ []
      where
      s' = 𝕊.wordsBy (_≟ ' ') s

open Reed
  using (
    reed
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{reed}.\ jenai zo'e bau la .lojban.

\subsection{le cmene be le me'oi .\AgdaKeyword{module}.\ fancu}
ni'o zo .k.\ cmavlaka'i zo konkatena

.i zo .t.\ cmavlaka'i zo tolsti

.i cumki fa lo nu su'o da zo'u zo .g.\ cmavlaka'i da

\subsection{le ctaipe be le su'u la'oi .\F{reed}.\ mapti}

\begin{code}
module ReedVeritas where
  private
    k₁ : (x : Buffer)
       → (a : Buffer.F x)
       → Char
       → String
    k₁ _ a x = show (𝔽.toℕ a) ++ 𝕊.fromChar x

    k₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → Char
       → String
    k₂ _ a b x = f a ++ "," ++ f b ++ 𝕊.fromChar x
      where
      f = show ∘ 𝔽.toℕ

  ac : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmina a) ≡ reed x (k₁ x a 'a')
  ac = {!!}

  ic : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmini a) ≡ reed x (k₁ x a 'i')
  ic = {!!}

  mixer : (x : Buffer)
        → (a b : Buffer.F x)
        → (d : a 𝔽.≤ b)
        → just (Muvgau a b d) ≡ reed x (k₂ x a b 'm')
  mixer x a b d = sym $ begin
    reed x (k₂ x a b 'm') ≡⟨ refl ⟩
    reed x k2 ≡⟨ refl ⟩
    𝕃.head (𝕃.mapMaybe id RL) ≡⟨ {!!} ⟩
    𝕃.head (𝕃.mapMaybe id RL') ≡⟨ {!!} ⟩
    Reed.Re.t x k2 ≡⟨ refl ⟩
    _,ₘ_ (romoi k2) oglok >>= r2og ≡⟨ reldunsi'u romoim joglok ⟩
    _,ₘ_ (just 'm') (just $ (a , b) , d) >>= r2og ≡⟨ refl ⟩
    Reed.Re.g x a b d 'm' ≡⟨ refl ⟩
    just (Muvgau a b d) ∎
    where
    romoi = 𝕃.last ∘ 𝕊.toList
    r2og = λ (r' , (a , b) , z) → Reed.Re.g x a b z r'
    _,ₘ_ = (Data.Maybe.ap ∘₂ mapₘ) _,_
    k2 = k₂ x a b 'm'
    RL = Reed.No.t k2 ∷ Reed.Pa.t k2 ∷ Reed.Re.t x k2 ∷ nok ∷ []
      where
      nok = Reed.No.k $ 𝕊.wordsBy (_≟ ' ') k2
    RL' = nothing ∷ nothing ∷ Reed.Re.t x k2 ∷ nothing ∷ []
    oglok = orsygenturfa'i $ romoivimcu k2
    reldunsi'u : {a b : _} → {x z : _}
               → a ≡ b
               → x ≡ z
               → _,ₘ_ a x >>= r2og ≡ _,ₘ_ b z >>= r2og
    reldunsi'u refl refl = refl
    romoim : romoi k2 ≡ just 'm'
    romoim = {!!}
    joglok : oglok ≡_ $ just $ (a , b) , d
    joglok = {!!}
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning

  vim : (x : Buffer)
      → (a b : Buffer.F x)
      → (d : a 𝔽.≤ b)
      → just (Vimcu a b d) ≡ reed x (k₂ x a b 'd')
  vim = {!!}

  uip : (x : Buffer)
      → (s : String)
      → (c : Char)
      → ¬ (c ≡ ' ')
      → (let s' = 𝕊.fromChar c ++ s in
         just (Rejgau s') ≡ reed x ("w " ++ s'))
  uip x s c n = sym $ begin
    reed x ("w " ++ s') ≡⟨ w++s≡w++fs ▹ cong (reed x) ⟩
    reed x (unwords $ "w" ∷ f s') ≡⟨ {!!} ⟩
    k ("w" ∷ f s') ≡⟨ fs'≡v₁++v₂ ▹ cong (k ∘ _∷_ "w") ⟩
    k ("w" ∷ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R (unwords $ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R _ ≡⟨ fs'≡v₁++v₂ ▹ sym ▹ cong (j∘R ∘ unwords) ⟩
    j∘R (unwords $ f s') ≡⟨ unwords∘f s' ▹ cong j∘R ⟩
    j∘R s' ∎
    where
    open Reed.No using (k)
    s' = 𝕊.fromChar c ++ s
    f = 𝕊.wordsBy $ _≟ ' '
    v₁ = {!!}
    v₂ = {!!}
    j∘R = just ∘ Rejgau
    fs'≡v₁++v₂ : f s' ≡ v₁ ∷ v₂
    fs'≡v₁++v₂ = {!!}
    unwords = 𝕊.unwords
    unwords∘f : (s : String) → unwords (f s) ≡ s
    unwords∘f = {!!}
    open Reed
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
    w++s≡w++fs : "w " ++ s' ≡ unwords ("w" ∷ f s')
    w++s≡w++fs = {!!}

  uin : (x : Buffer)
      → reed x "w" ≡ mapₘ Rejgau (Buffer.datnyveicme x)
  uin x = begin
    reed x "w" ≡⟨ refl ⟩
    𝕃.head (𝕃.mapMaybe id L) ≡⟨ duridos ⟩
    𝕃.head (𝕊.toList "w") >>= Reed.No.g ≡⟨ refl ⟩
    mapₘ Rejgau (Buffer.datnyveicme x) ∎
    where
    open Reed
    ridos = 𝕃.head (𝕊.toList "w") >>= Reed.No.g
    L = ridos ∷ _
    duridos : 𝕃.head (𝕃.mapMaybe id L) ≡ ridos
    duridos with ridos
    ... | just _ = refl
    ... | nothing = refl
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning

  -- ni'o la .varik. cu stidi lo nu tcidu le velcki be
  -- la .uin. fa lo na jimpe be fi la .kybin. je la'oi
  -- .kybin'.

  kybin : (x : Buffer)
        → reed x "q" ≡ just Sisti
  kybin x with 𝕃.head (𝕊.toList "q") >>= Reed.No.g
  ... | just _ = refl
  ... | nothing = refl

  kybin' : (x : Buffer)
         → reed x "Q" ≡ just Sisti!
  kybin' x with 𝕃.head (𝕊.toList "Q") >>= Reed.No.g
  ... | just _ = refl
  ... | nothing = refl

  xon : (x : Buffer)
      → (z : Σ ℕ $ λ n → ℕ.suc n ≡ length (Buffer.citri x))
      → reed x "u" ≡ just (Xruti $ mink 𝔽.zero $ proj₂ z)
  xon x z = begin
    reed x "u" ≡⟨ {!!} ⟩
    mapₘ X (𝕃.head $ 𝕃.allFin _) ≡⟨ dzeroxe z ▹ cong (mapₘ X) ⟩
    just (X $ mink 𝔽.zero $ proj₂ z) ∎
    where
    X = Xruti
    dzeroxe : {n : ℕ}
            → (z : Σ ℕ $ (_≡ n) ∘ ℕ.suc)
            → 𝕃.head (𝕃.allFin n) ≡ just (mink 𝔽.zero $ proj₂ z)
    dzeroxe (_ , refl) = refl
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
\end{code}

\section{la \F{kanji}}
ni'o la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ .orsi li re lo jalge be lo nu co'e la'oi .\B s.\ la'oi .\B x.\ kei zo'e poi ga jonai ke'a du la'oi .\IC{nothing}.\ gi ga jonai cadga fa lo nu cusku ke'a fo lo co'e co mu'oi glibau.\ standard output .glibau.\ gi\ldots ga je co'e gi la .varik.\ na birti lo du'u zabna ciksi fo ma kau bau la .lojban.  .i ku'i gu zabna ciksi bau la .lojban.\ gi ciksi le ctaipe be le su'u mapti

\begin{code}
kanji : {x : Buffer}
      → Cmd x
      → Σ Buffer $ Maybe ∘ _⊎_ String ∘ Cmdᵢₒ
kanji {x} Sisti = x ,_ $ just $ inj₂ Sistiᵢₒ
kanji {x} (Jmina a) = x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" a
kanji {x} (Cusku a b _) = x ,_ $ just $ inj₁ $ unlines $ i BL
  where
  BL = Buffer.lerpinste x
  i = _↓_ (𝔽.toℕ a) ∘ _↑_ (𝔽.toℕ b ℕ.+ 1)
kanji {x} (Namcusku a b m) = x ,_ $ just $ inj₁ $ viiet kot
  where
  kot = from-inj₁ $ from-just $ proj₂ $ kanji {x} $ Cusku a b m
  viiet = unlines ∘ 𝕃.map stringCat' ∘ uin ∘ lines
    where
    stringCat' = λ (x , z) → show x ++ "\t" ++ z
    uin : List String → List $ ℕ × String
    uin = 𝕃.zip $ _↓_ (𝔽.toℕ a) $ 𝕃.upTo $ 𝔽.toℕ b ℕ.+ 1
kanji {x} (Muvgau a b _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = mink (Buffer.cablerpinsle x) {!!};
    lerpinste = {!!}
    }
kanji {x} (Vimcu a b _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = {!!};
    lerpinste = 𝕃.map proj₂ $ 𝕃.filter nin $ indice Lz}
    where
    Lz = Buffer.lerpinste x
    indice = λ x → 𝕃.zip (𝕃.allFin $ length x) x
    nin : (x : _)
        → (Dec $ _∉_ ⦃ liliList ⦄ ⦃ record {_≟_ = 𝔽._≟_} ⦄
            (proj₁ x)
            (𝕃.map
              (flip 𝔽.inject≤ $ DFP.toℕ≤n _)
              (_↓_ (𝔽.toℕ a) $ 𝕃.allFin $ 𝔽.toℕ b)))
    nin _ = _ ≟ _
kanji = {!!}
\end{code}

\subsection{le ctaipe be le su'u la \F{kanji}\ cu mapti}

\begin{code}
module KanjyVeritas where
  dub₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → (d : a 𝔽.≤ b)
       → let K = λ f → kanji $ f a b d in
         let i = _≡_ x ∘ proj₁ ∘ K in
         i Cusku × i Namcusku
  dub₂ _ _ _ _ = refl , refl

  jminac : (x : Buffer)
         → (a : Buffer.F x)
         → (_≡_
             (kanji {x} $ Jmina a)
             (x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" a))
  jminac _ _ = refl

  nilzilcmiv : (x : Buffer)
             → (a b : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → (_≡_
                 (length $ Buffer.lerpinste
                   (proj₁ $ kanji {x} $ Vimcu a b d))
                 (ℕ._∸_
                   (length $ Buffer.lerpinste x)
                   (ℕ.suc $ 𝔽.toℕ a ℕ.∸ 𝔽.toℕ b)))
  nilzilcmiv = {!!}

  pindices : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let K = proj₂ $ kanji {x} $ Cusku a b d in
             let L = lines $ from-inj₁ $ from-just K in
             let Lx = Buffer.lerpinste x in
             (n : Fin $ length L)
           → (Σ
               (𝔽.toℕ n ℕ.+ 𝔽.toℕ a ℕ.< length Lx)
               (λ ℓ → L ! n ≡ Lx ! 𝔽.fromℕ< ℓ))
  pindices x a b d n = {!!} , {!!}

  muvdusin : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let x' = proj₁ $ kanji {x} $ Muvgau a b d in
             (kanji {x} (Muvgau a b d) ≡ (x' , nothing))
           × (Σ
               ((_≡_ on (length ∘ Buffer.lerpinste)) x x')
               (λ e →
                 (_≡_
                   (Buffer.lerpinste x ! a)
                   (Buffer.lerpinste x' ! mink a e))))
           × let L = Buffer.lerpinste in
             (_≡_ on (_↑_ (𝔽.toℕ a ℕ.⊓ 𝔽.toℕ b) ∘ L)) x x'
           × (_≡_ on (_↓_ (𝔽.toℕ a ℕ.⊔ 𝔽.toℕ b) ∘ L)) x x'
  muvdusin = {!!}

  xrutis : (x : Buffer)
         → (n : Fin $ length $ Buffer.citri x)
         → (_≡_
             (kanji {x} $ Xruti n)
             (let x' = Buffer.citri x ! n in
              (_,_
                record x {
                  lerpinste = proj₁ x';
                  cablerpinsle = proj₂ x';
                  citri = {!!}}
                nothing)))
  xrutis = {!!}

  vimcus : (x : Buffer)
         → (a b : Buffer.F x)
         → (d : a 𝔽.≤ b)
         → (Σ
             (∃ $ Fin ∘ length)
             (λ (L , I)
               → (_≡_
                   (kanji {x} $ Vimcu a b d)
                   (_,_
                     record x {
                       lerpinste = L;
                       cablerpinsle = I
                     }
                     nothing))
               × (_≡_
                   (length L)
                   (ℕ._∸_
                     (length $ Buffer.lerpinste x)
                     (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a ℕ.+ 1)))
               × I ≡ {!!}))
  vimcus = {!!}
\end{code}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift snurytcati IO.>> getArgs IO.>>= uic ∘ 𝕃.head
  where
  postulate snurytcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-# COMPILE GHC snurytcati = plegg [RPath, WPath, Stdio] #-}
  uic : Maybe String → IO ⊤
  uic = (IO._>>= ⟲) ∘ maybe mkDef (IO.pure def)
    where
    def = record {
      datnyveicme = nothing;
      lerpinste = "" ∷ List.[];
      cablerpinsle = 𝔽.zero;
      citri = List.[];
      rejgaudatni = nothing
      }
    mkDef : _
    mkDef c = uit ∘ 𝕊.lines IO.<$> readFile c
      where
      uit : _ → _
      uit [] = record def {datnyveicme = just c}
      uit x@(_ ∷ _) = record {
        datnyveicme = just c;
        lerpinste = x;
        cablerpinsle = 𝔽.opposite 𝔽.zero;
        citri = List.[];
        rejgaudatni = just c
        }
    ⟲ : Buffer → IO ⊤
    ⟲ x = IO.getLine IO.>>= f ∘ reed x
      where
      f : Maybe $ Cmd x → IO ⊤
      f nothing = IO.putStrLn "?" IO.>> ⟲ x
      f (just c) with kanji c
      ... | x' , nothing = ⟲ x'
      ... | x' , just (inj₁ z) = IO.putStrLn z IO.>> ⟲ x'
      ... | x' , just (inj₂ z) with z
      ... | Sisti!ᵢₒ = IO.pure _
      ... | Skamiᵢₒ a = {!!}
      ... | Tciduᵢₒ a b = {!!}
      ... | Rejgauᵢₒ a b = IO.writeFile a b IO.>> ⟲ x
      ... | Sistiᵢₒ = f $ mapₘ (λ _ → Sisti!) $ decToMaybe $ r ≟ c₁
        where
        r = Buffer.rejgaudatni x'
        c₁ = mapₘ (unlines ∘ proj₁) $ 𝕃.head $ Buffer.citri x'
\end{code}
\end{document}
