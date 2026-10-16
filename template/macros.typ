// 1. אלומות נפוצות
#let cA = math.cal("A")
#let cB = math.cal("B")
#let cC = math.cal("C")
#let cD = math.cal("D")
#let cE = math.cal("E")
#let cF = math.cal("F")
#let cG = math.cal("G")
#let cH = math.cal("H")
#let cI = math.cal("I")
#let cJ = math.cal("J")
#let cK = math.cal("K")
#let cL = math.cal("L")
#let cM = math.cal("M")
#let cN = math.cal("N")
#let cO = math.cal("O")
#let cP = math.cal("P")
#let cQ = math.cal("Q")
#let cT = math.cal("T")
#let cU = math.cal("U")

#let frA = math.frak("A")   // אידיאלים / חוגים מקומיים
#let frM = math.frak("m")
#let frP = math.frak("p")


//------------------------------------------------------------------
// 2. פעולות בסיסיות על אלומות
// ---------------------------------------------------------------------
#let shf(F) = math.attach(F, tr: [+])            // אילום (sheafification)
#let Sh = math.op("Sh")
#let PSh = math.op("PSh")
#let Ab = math.op("Ab")
#let Vect = math.op("Vect")
#let Coh = math.op("Coh")
#let QCoh = math.op("QCoh")
#let Loc = math.op("Loc")                        // מערכות מקומיות
#let Perv = math.op("Perv")
#let Mod = math.op("Mod")
#let Cx = math.op("Ch")                          // קומפלקסי שרשרת (לא "Ch" – ראה §9)
#let Kcat = math.op("K")                         // קטגוריית ההומוטופיה
#let supp = math.op("supp")
#let sing = math.op("Sing")
#let rk = math.op("rk")
#let gr = math.op("gr")
#let ann = math.op("Ann")

#let globalSect(U, F) = $Gamma(#U, #F)$                // חתכים מעל U
#let sectc(U, F) = $Gamma_c (#U, #F)$            // חתכים עם תומך קומפקטי
#let rest(s, V) = $lr(#s|)_#V$                   // צמצום חתך
#let stalk(F, x) = math.attach(F, br: x)         // גבעול
#let germ(s, x) = math.attach(s, br: x)
#let constsh(M) = $underline(#M)$                // אלומה קבועה
#let ringed(X, O: cO) = $(#X, #O_#X)$

// גבולות ישרים/הפוכים (עם החץ *מתחת* ל-lim גם inline)
#let dirlim = $limits(lim)_(arrow.r.long)$
#let invlim = $limits(lim)_(arrow.l.long)$
#let colim = math.op(math.limits[colim])

// ---------------------------------------------------------------------
// 2. שמות קטגוריות (\Set, \Ab, …) — bold upright
// ---------------------------------------------------------------------
#let Set  = math.bold("Set")
#let Ab   = math.bold("Ab")
#let Grp  = math.bold("Grp")
#let Top  = math.bold("Top")
#let Cat  = math.bold("Cat")
#let Vect = math.bold("Vect")
#let RMod = $R"-" bold("Mod")$        // \RMod  =  R-Mod
#let ModR = $bold("Mod") "-"R$        // \ModR  =  Mod-R
#let ZMod = $ZZ"-" bold("Mod")$
#let Ch   = math.op("Ch")             // קטגוריית קומפלקסי השרשרת

// ---------------------------------------------------------------------
// 3. Hom, מכפלות טנזוריות, פונקטורים
// ---------------------------------------------------------------------
#let Hom = math.op("Hom")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let Ext = math.op("Ext")
#let Tor = math.op("Tor")
#let sHom = math.op($cal(H)"om"$)                // אלומת Hom (פנימית)
#let RHom = math.op("RHom")
#let RsHom = math.op($R cal(H)"om"$)
#let Cone = math.op("Cone")
#let Fib = math.op("Fib")
#let Tot = math.op("Tot")
#let ds   = math.plus.o     
#let otO = math.class("binary", $times.o_(cal(O)_X)$)          // ⊗_{O_X}
#let otL = math.class("binary", math.attach($times.o$, tr: $bold(L)$))  // ⊗^L
#let otLO = math.class("binary", math.attach($times.o$, tr: $bold(L)$, br: $cal(O)_X$))
#let otD = math.class("binary", $times.o_(cal(D)_X)$)          // ⊗ מעל D_X
#let otLD = math.class("binary", math.attach($times.o$, tr: $bold(L)$, br: $cal(D)_X$))
#let bds  = math.plus.o.big           // \bigoplus ⨁  (0.15: plus.circle.big הוסר)

#let iso  = math.tilde.equiv          // \cong    ≅
#let into = math.arrow.r.hook         // \hookrightarrow  ↪
#let onto = math.arrow.r.twohead      // \twoheadrightarrow ↠
// ---------------------------------------------------------------------
// 3. אופרטורים (\operatorname{...})
// ---------------------------------------------------------------------
#let Hom   = math.op("Hom")
#let Homr  = $op("Hom")_R$
#let Homz  = $op("Hom")_ZZ$
#let End   = math.op("End")
#let Ext   = math.op("Ext")
#let Tor   = math.op("Tor")
#let im    = math.op("im")
#let Im    = math.op("Im")
#let coker = math.op("coker")
#let Coker = math.op("Coker")
#let Ker   = math.op("Ker")
#let ker   = math.op("ker")
#let coim  = math.op("coim")
#let ob    = math.op("ob")
#let id    = math.op("id")
#let Fun   = math.op("Fun")
#let cone  = math.op("cone")
#let Tot   = math.op("Tot")
#let colim = math.op("colim")
#let Spec  = math.op("Spec")
#let Bil   = math.op("Bil")

// ---------------------------------------------------------------------
// 4. שש הפונקטורים ופונקטורים נגזרים
// ---------------------------------------------------------------------
#let push(f, F) = $#f _* #F$                      // f_* F   (זהיר: ראה הערה בקובץ)
#let Rpush(f) = $R attach(#f, b: *)$            // Rf_*
#let Rpushc(f) = $R attach(#f, b: !)$           // Rf_!
#let Lpull(f) = $L attach(#f, tr: *)$            // Lf^*
#let pull(f) = math.attach(f, tr: [\*])          // f^*
#let ushr(f) = math.attach(f, tr: [!])           // f^!  (הפונקטור החריג)
#let lsh(f) = math.attach(f, br: [!])            // f_!
#let RGam = math.op($R Gamma$)
#let RGamc = math.op($R Gamma_c$)
#let RGamZ(Z) = $R Gamma_#Z$                     // קוהומולוגיה מקומית
#let invimg(f, G) = $#f^(-1) #G$                    // f^{-1} G  (העתקה הפוכה טופולוגית)

// דואליות ורדייה ואלומה דואלית
#let VD = math.op($bold(D)$)                     // D(-)  = הדואל של ורדייה
#let VDX(X) = $bb(D)_#X$
#let dualz(X) = $omega_#X$                       // ω_X — הקומפלקס הדואליזציה
#let IC = math.op("IC")
#let ICs(X, L) = $"IC"_#X (#L)$
#let midext = $j_(!*)$                           // הרחבה ביניים j_{!*}

// מחזורים קרובים/נעלמים
#let nearby(f) = math.attach(math.psi, br: f)          // ψ_f
#let vanish(f) = math.attach(math.phi, br: f)          // φ_f
#let pnearby(f) = math.attach(math.psi, tl: [p], br: f) // ^pψ_f
#let pvanish(f) = math.attach(math.phi, tl: [p], br: f) // ^pφ_f

// ---------------------------------------------------------------------
// 5. קטגוריות נגזרות ומשולשות
// ---------------------------------------------------------------------
#let Der(A) = $D(#A)$
#let Db  = $D^b $
#let Dp  = $D^(+) $
#let Dm  = $D^(-) $
#let Dbc = $D_c^b $                     // קונסטרוקטיבילי
#let Dbqc(X) = $D_"qc"^b (#X)$
#let Dbcoh(X) = $D_"coh"^b (#X)$
#let Dbhol(X) = $D_"hol"^b (#X)$
#let Dbrh(X) = $D_"rh"^b (#X)$                   // הולונומי רגולרי
#let Dcon(X, k) = $D_c^b (#X; #k)$

#let shift(F, n) = $#F [#n]$                     // הזזה F[n]
#let cone(f) = $"Cone"(#f)$
#let HomD(X, F, G) = $"Hom"_(D(#X)) (#F, #G)$
#let ExtD(i, X, F, G) = $"Ext"^#i _(#X) (#F, #G)$

// t-מבנים
#let tle(n) = $tau_(<= #n)$
#let tge(n) = $tau_(>= #n)$
#let ptle(n) = math.attach(math.tau, tl: [p], br: $<= #n$)   // ^pτ_{≤n}
#let ptge(n) = math.attach(math.tau, tl: [p], br: $>= #n$)   // ^pτ_{≥n}
#let Dle(n) = $D^(<= #n)$
#let Dge(n) = $D^(>= #n)$
#let pDle(n) = math.attach(math.upright("D"), tl: [p], tr: $<= #n$)
#let pDge(n) = math.attach(math.upright("D"), tl: [p], tr: $>= #n$)
#let heart = $suit.heart$                        // הלב של ה-t-מבנה
#let pH(i) = math.attach(math.upright("H"), tl: [p], tr: i)  // ^pH^i — קוהומולוגיה סוטה
#let coh(i, X, F) = $H^#i (#X, #F)$              // H^i(X, F)   (לא "H"! ראה §9)
#let cohc(i, X, F) = $H_c^#i (#X, #F)$
#let cechH(i, U, F) = $caron(H)^#i (#U, #F)$
#let cechC(U, F) = $caron(C)^bullet (#U, #F)$
#let hyper(i, F) = $bb(H)^#i (#F)$               // היפר-קוהומולוגיה

// ---------------------------------------------------------------------
// 6. D-מודולים
// ---------------------------------------------------------------------
#let DX(X) = $cal(D)_#X$
#let Dop = $cal(D)$
#let DYX = $cal(D)_(Y arrow.r X)$                // הבימודול המעביר
#let DXY = $cal(D)_(X arrow.l Y)$
#let DR = math.op("DR")
#let Sol = math.op("Sol")
#let Char = math.op("Char")                      // יריעה אופיינית
#let SS = math.op("SS")                          // singular support
#let Ch = math.op("Ch")
#let holo = $"hol"$
#let dint(f) = $integral_#f$                     // אינטגרל ישיר ∫_f
#let dpull(f) = math.attach(f, tr: [†])          // f^†
#let Fgr(i) = $F_#i$                             // סינון
#let grF = $"gr"^F$
#let Omeg(X) = $Omega_#X$
#let Theta(X) = $Theta_#X$                       // שדות וקטוריים

#let xto(l) = math.class("relation", $limits(arrow.r.long)^#l$)

// 6. קטגוריות והעתקות
#let Hom = $op("Hom")$
#let sHom = $cal(H)o m$ // אלומת Hom
#let Sh(X) = $op("Sh")(#X)$ // קטגוריית האלומות
#let PSh(X) = $op("PSh")(#X)$ // קטגוריית קדם-האלומות
#let cohsh(x, K) = $cal(H)^#x (#K)$

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let sect = math.inter
#let triangle(A, B, C, f, g, h) = diagram(
  spacing: 1.5cm,
  node((0,1), A), node((2, 1), B), node((1, 2), C),
  edge((0, 1), (2, 1), "->", label: f, label-side: left),  // מחוץ, משמאל־מעל
  edge((2, 1), (1, 2), "->", label: g, label-side: left),   // מחוץ, מימין־מעל
  edge((1, 2), (0, 1), "->", label: h, label-side: left),  // מתחת לבסיס  ← התיקון
)

#let square(A, B, C, D, f: none, g: none, h: none, k: none) = diagram(
  spacing: 2.2cm,
  node((0, 0), A), node((1, 0), B),
  node((0, 1), C), node((1, 1), D),
  edge((0, 0), (1, 0), "->", label: f, label-side: left),   // מעל
  edge((0, 0), (0, 1), "->", label: g, label-side: right),  // משמאל
  edge((1, 0), (1, 1), "->", label: h, label-side: left),   // מימין
  edge((0, 1), (1, 1), "->", label: k, label-side: right),  // מתחת
)

#let chain5(O1, O2, O3, O4, O5, f1, f2, f3, f4) = diagram(   // הגדרה אחת בלבד
  spacing: 1.6cm,
  node((0, 0), O1), node((1, 0), O2), node((2, 0), O3),
  node((3, 0), O4), node((4, 0), O5),
  edge((0, 0), (1, 0), "->", label: f1),
  edge((1, 0), (2, 0), "->", label: f2),
  edge((2, 0), (3, 0), "->", label: f3),
  edge((3, 0), (4, 0), "->", label: f4),
)

#let ses(A, B, C, f: none, g: none) = chain5($0$, A, B, C, $0$, none, f, g, none)

#let placed(X, n) = math.attach(X, br: $[#n]$)


// --- 7. אלומות מיוחדות ומרחבים מחוגים ---
#let cI = $cal(I)$ // אלומת אידיאלים
#let constSh(M) = $underline(#M)$ // אלומה קבועה
#let ringed(X, O: cO) = $(#X, #O _#X)$ // זוג של מרחב מחוג
// --- 8. פעולות נוספות ---
#let supp = $op("supp")$ // תמיכה
#let tensorO = math.class("binary", $times.o _(cal(O))$)
// --- 9. קוהומולוגיה ---
// הסרנו את הסולמיות. Typst יודע ש-i, X, F הם משתנים שהועברו לפונקציה.
// --- 9. קוהומולוגיה ---
#let H(i, X, F) = $H^#i (#X, #F)$ 
#let CechH(i, U, F) = $caron(H)^#i (#U, #F)$
#let CechC(U, F) = $caron(C)^bullet (#U, #F)$

// --- 10. סדרה מדויקת קצרה (מבוסס על chain5 שלך) ---
// שימוש ב-none במקום "" עבור חיצים ללא תווית
#let ses(A, B, C, f: none, g: none) = {
  chain5($0$, A, B, C, $0$, none, f, g, none)
}
//11. long words
#let cons = "constructible"
#let con = "continuous"
#let shff = "sheafification"
#let nbr = "neighborhood" 
#let nbrs = "neighborhoods" 


// ---------------------------------------------------------------------
// Editing markup: text added or rephrased in the current revision is
// coloured blue.  Remove by replacing "#ed[" ... "]" wrappers or by
// redefining ed to the identity: #let ed(body) = body
// ---------------------------------------------------------------------
#let ed(body) = text(body)