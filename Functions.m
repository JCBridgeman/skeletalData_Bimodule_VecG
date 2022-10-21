(* ::Package:: *)

(* ::Section::Closed:: *)
(*Formatting etc.*)


polarForm=Expand[#/.z_?NumericQ:>Abs[z] Exp[I Arg[z]]]&;


(* ::Section::Closed:: *)
(*Helpful definitions*)


Unprotect[Abs,Conjugate,Power];
Abs[\[Phi][a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]]:=1
Conjugate[\[Phi][a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]]:=1/\[Phi][a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]

Abs[\[Phi][a_,b_][c_][\[Alpha]0_,\[Beta]0_]]:=1
Conjugate[\[Phi][a_,b_][c_][\[Alpha]0_,\[Beta]0_]]:=1/\[Phi][a,b][c][\[Alpha]0,\[Beta]0]

Abs[\[CurlyPhi][x_][a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]]:=1
Conjugate[\[CurlyPhi][x_][a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]]:=1/\[CurlyPhi][x][a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]

\[CurlyPhi][x_][a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]^y_/;(y<0||y>=x):=\[CurlyPhi][x][a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]^Mod[y,x]

Abs[\[CurlyPhi][x_][a_,b_][c_][\[Alpha]0_,\[Beta]0_]]:=1
Conjugate[\[CurlyPhi][x_][a_,b_][c_][\[Alpha]0_,\[Beta]0_]]:=1/\[CurlyPhi][x][a,b][c][\[Alpha]0,\[Beta]0]

\[CurlyPhi][x_][a_,b_][c_][\[Alpha]0_,\[Beta]0_]^y_/;(y<0||y>=x):=\[CurlyPhi][x][a,b][c][\[Alpha]0,\[Beta]0]^Mod[y,x]

Abs[\[Phi][a_,b_][c_]]:=1
Conjugate[\[Phi][a_,b_][c_]]:=1/\[Phi][a,b][c]
Protect[Abs,Conjugate,Power];


coeff[v_,basis_]:=Switch[!FreeQ[basis,Plus]||!FreeQ[basis,Times],True,
Block[{stdbasis,M,sol},
stdbasis=Variables[basis];
M=Table[coeff[x,stdbasis],{x,basis}];
sol=LinearSolve[Transpose[M],coeff[v,stdbasis]];
Return[sol]
]
,
False,
Table[Coefficient[v,x],{x,basis}]
];(*Assume orthogonal basis*)


(* ::Section::Closed:: *)
(*Fusion Rings*)


fusionProduct[a_,b_]/;ContainsAll[obsC,{a,b}]:=fusionProduct[a,b]=Select[obsC,V[a,b][#]!=0&]
fusionProduct[a_,b_]/;ContainsAll[obsD,{a,b}]:=fusionProduct[a,b]=Select[obsD,V[a,b][#]!=0&]
fusionProduct[a_,b_]/;((MemberQ[obsC,a]&&MemberQ[obsM,b])||(MemberQ[obsM,a]&&MemberQ[obsD,b])):=fusionProduct[a,b]=Select[obsM,V[a,b][#]!=0&]

If[!ValueQ[unitC],unitC:=unitC=Do[If[DeleteDuplicates[Flatten[Table[fusionProduct[a,u]=={a}==fusionProduct[u,a],{a,obsC}]]]=={True},Return[u]],{u,obsC}]];
If[!ValueQ[unitD],unitD:=unitD=Do[If[DeleteDuplicates[Flatten[Table[fusionProduct[a,u]=={a}==fusionProduct[u,a],{a,obsD}]]]=={True},Return[u]],{u,obsD}]];

dim[a_,A_]/;MemberQ[A,a]:=dim[a,A]=Module[{d0,dimeqs,dimsol,da},
dimeqs=Join[
Outer[d0[#1]d0[#2]==Sum[V[#1,#2][x]d0[x],{x,fusionProduct[#1,#2]}]&,A,A]//Flatten
,d0[#]>=1&/@A];
da:=d0[a]//.Solve[dimeqs][[1]]//RootReduce//FullSimplify//ToRadicals;
Return[da]];

dim[a_]/;MemberQ[obsC,a]:=dim[a,obsC]
dim[a_]/;MemberQ[obsD,a]:=dim[a,obsD]

dim[a_]/;MemberQ[obsM,a]:=dim[a]=Module[{d0,dimeqs,dimsol,da},
dimeqs=Join[
Outer[dim[#1]d0[#2]==Sum[V[#1,#2][x]d0[x],{x,fusionProduct[#1,#2]}]&,obsC,obsM]//Flatten
,d0[#]>=1&/@obsM,{Total[d0[#]^2&/@obsM]==dtot["C"]^2}];
da:=d0[a]//.Solve[dimeqs][[1]]//RootReduce//FullSimplify//ToRadicals;
Return[da]];

dtot["C"|0]:=Sqrt[Total[dim[#]^2&/@obsC]]//RootReduce//FullSimplify//ToRadicals
dtot["D"|4]:=Sqrt[Total[dim[#]^2&/@obsD]]//RootReduce//FullSimplify//ToRadicals

dual[a_]/;MemberQ[obsC,a]:=Module[{v=Abs[V[a,#][unitC]]&/@obsC},obsC[[Position[v,1][[1,1]]]]]
dual[a_]/;MemberQ[obsD,a]:=Module[{v=Abs[V[a,#][unitD]]&/@obsD},obsD[[Position[v,1][[1,1]]]]]


fusionTable[A_,B_]:=Module[{fp},
TableForm[
Table[
fp=Flatten[Table[ConstantArray[c,V[a,b][c]],{c,fusionProduct[a,b]}]];
If[Length[fp]==1,objNames[fp[[1]]],CirclePlus@@(objNames[#]&/@fp)]
,{a,A},{b,B}]
,
TableHeadings->{objNames[#]&/@A,objNames[#]&/@B},TableAlignments->Center]
]

fusionTable["C"]:=fusionTable[obsC,obsC]
fusionTable["L"]:=fusionTable[obsC,obsM]
fusionTable["R"]:=fusionTable[obsM,obsD]
fusionTable["D"]:=fusionTable[obsD,obsD]


(* ::Section:: *)
(*F-symbols*)


F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:=0

F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsC,a]&&MemberQ[obsC,b]&&MemberQ[obsC,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.FData[0]

F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsC,a]&&MemberQ[obsC,b]&&MemberQ[obsM,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.FData[1]

F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsC,a]&&MemberQ[obsM,b]&&MemberQ[obsD,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.FData[2]

F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsM,a]&&MemberQ[obsD,b]&&MemberQ[obsD,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.FData[3]

F[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsD,a]&&MemberQ[obsD,b]&&MemberQ[obsD,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.FData[4]

Fs[A_,B_,C_]:=Table[F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0],{a,A},{b,B},{c,C},{e,fusionProduct[a,b]},{f,fusionProduct[b,c]},{d,Intersection[fusionProduct[a,f],fusionProduct[e,c]]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]},{\[Mu]0,V[b,c][f]},{\[Nu]0,V[a,f][d]}]//Flatten

newF[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:=Sum[
Q[a,f][d][\[Tau]0,\[Nu]0]Q[b,c][f][\[Sigma]0,\[Mu]0]Conjugate[Q[e,c][d][\[Delta]0,\[Beta]0]Q[a,b][e][\[Gamma]0,\[Alpha]0]]F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0],{\[Gamma]0,V[a,b][e]},{\[Delta]0,V[e,c][d]},{\[Tau]0,V[a,f][d]},{\[Sigma]0,V[b,c][f]}
]
newFs[A_,B_,C_]:=Table[newF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0],{a,A},{b,B},{c,C},{e,fusionProduct[a,b]},{f,fusionProduct[b,c]},{d,Intersection[fusionProduct[a,f],fusionProduct[e,c]]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]},{\[Mu]0,V[b,c][f]},{\[Nu]0,V[a,f][d]}]//Flatten
Q[a_,b_][c_][\[Alpha]0_,\[Beta]0_]/;V[a,b][c]==1:=\[Phi][a,b][c]

Fs["C"|0]:=Fs[obsC,obsC,obsC]
Fs["L"|1]:=Fs[obsC,obsC,obsM]
Fs["\[CapitalOmega]"|2]:=Fs[obsC,obsM,obsD]
Fs["R"|3]:=Fs[obsM,obsD,obsD]
Fs["D"|4]:=Fs[obsD,obsD,obsD]

newFs["C"|0]:=newFs[obsC,obsC,obsC]
newFs["L"|1]:=newFs[obsC,obsC,obsM]
newFs["\[CapitalOmega]"|2]:=newFs[obsC,obsM,obsD]
newFs["R"|3]:=newFs[obsM,obsD,obsD]
newFs["D"|4]:=newFs[obsD,obsD,obsD]

\[Kappa][x_]/;MemberQ[obsC,x]:=F[x,dual[x],x][x][1,unitC,1][1,unitC,1]dim[x]//FullSimplify
\[Kappa][x_]/;MemberQ[obsD,x]:=F[x,dual[x],x][x][1,unitD,1][1,unitD,1]dim[x]//FullSimplify

NF[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Sigma]0_,f_,\[Tau]0_]:=NF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0,f,\[Tau]0]=N[F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0,f,\[Tau]0],20]

NFs[A_,B_,C_]:=Table[NF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0],{a,A},{b,B},{c,C},{e,fusionProduct[a,b]},{f,fusionProduct[b,c]},{d,Intersection[fusionProduct[a,f],fusionProduct[e,c]]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]},{\[Mu]0,V[b,c][f]},{\[Nu]0,V[a,f][d]}]//Flatten

NFs["C"|0]:=NFs[obsC,obsC,obsC]
NFs["L"|1]:=NFs[obsC,obsC,obsM]
NFs["\[CapitalOmega]"|2]:=NFs[obsC,obsM,obsD]
NFs["R"|3]:=NFs[obsM,obsD,obsD]
NFs["D"|4]:=NFs[obsD,obsD,obsD]

N\[Kappa][x_]/;MemberQ[obsC,x]:=NF[x,dual[x],x][x][1,unitC,1][1,unitC,1]dim[x]//FullSimplify
N\[Kappa][x_]/;MemberQ[obsD,x]:=NF[x,dual[x],x][x][1,unitD,1][1,unitD,1]dim[x]//FullSimplify


leftBasis[a_,b_,c_][d_]:=Flatten[Table[{\[Alpha]0,e,\[Beta]0},{e,Select[fusionProduct[a,b],V[#,c][d]>0&]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]}],2]
rightBasis[a_,b_,c_][d_]:=Flatten[Table[{\[Sigma]0,f,\[Tau]0},{f,Select[fusionProduct[b,c],V[a,#][d]>0&]},{\[Sigma]0,V[b,c][f]},{\[Tau]0,V[a,f][d]}],2]

Fblk[a_,b_,c_][d_]:=
Table[
F[a,b,c][d][l[[1]],l[[2]],l[[3]]][r[[1]],r[[2]],r[[3]]],
{l,leftBasis[a,b,c][d]},{r,rightBasis[a,b,c][d]}
]

NFblk[a_,b_,c_][d_]:=
Table[
NF[a,b,c][d][l[[1]],l[[2]],l[[3]]][r[[1]],r[[2]],r[[3]]],
{l,leftBasis[a,b,c][d]},{r,rightBasis[a,b,c][d]}
]


(* ::Section::Closed:: *)
(*Pentagons*)


chkPent[A_,B_,C_,D_]:=(Flatten[Table[
RootReduce[
Sum[F[a5,a2,a3][a4][\[Alpha]1,a6,\[Alpha]2][\[Gamma]0,c0,\[Delta]0]F[a0,a1,c0][a4][\[Alpha]0,a5,\[Delta]0][\[Gamma]1,c1,\[Gamma]2],{\[Delta]0,V[a5,c0][a4]}]
-
Sum[F[a0,a1,a2][a6][\[Alpha]0,a5,\[Alpha]1][\[Beta]0,b0,\[Beta]1]F[a0,b0,a3][a4][\[Beta]1,a6,\[Alpha]2][\[Beta]2,c1,\[Gamma]2]F[a1,a2,a3][c1][\[Beta]0,b0,\[Beta]2][\[Gamma]0,c0,\[Gamma]1],{b0,Select[fusionProduct[a1,a2],V[a0,#][a6]>0&&V[#,a3][c1]>0&]},{\[Beta]0,V[a1,a2][b0]},{\[Beta]1,V[a0,b0][a6]},{\[Beta]2,V[b0,a3][c1]}]
]==0
,
{a0,A},{a1,B},{a2,C},{a3,D},{a5,fusionProduct[a0,a1]},{a6,fusionProduct[a5,a2]},{a4,fusionProduct[a6,a3]},{c0,fusionProduct[a2,a3]},{c1,Select[fusionProduct[a1,c0],V[a0,#][a4]>0&]},
{\[Alpha]0,V[a0,a1][a5]},{\[Alpha]1,V[a5,a2][a6]},{\[Alpha]2,V[a6,a3][a4]},{\[Gamma]0,V[a2,a3][c0]},{\[Gamma]1,V[a1,c0][c1]},{\[Gamma]2,V[a0,c1][a4]}
]]//DeleteDuplicates)

chkPent["C"|0]:=chkPent[obsC,obsC,obsC,obsC]
chkPent["L"|1]:=chkPent[obsC,obsC,obsC,obsM]

pentagonQ[A_,B_,C_,D_]:={True}==(Flatten[Table[
RootReduce[
Sum[F[a5,a2,a3][a4][\[Alpha]1,a6,\[Alpha]2][\[Gamma]0,c0,\[Delta]0]F[a0,a1,c0][a4][\[Alpha]0,a5,\[Delta]0][\[Gamma]1,c1,\[Gamma]2],{\[Delta]0,V[a5,c0][a4]}]
-
Sum[F[a0,a1,a2][a6][\[Alpha]0,a5,\[Alpha]1][\[Beta]0,b0,\[Beta]1]F[a0,b0,a3][a4][\[Beta]1,a6,\[Alpha]2][\[Beta]2,c1,\[Gamma]2]F[a1,a2,a3][c1][\[Beta]0,b0,\[Beta]2][\[Gamma]0,c0,\[Gamma]1],{b0,Select[fusionProduct[a1,a2],V[a0,#][a6]>0&&V[#,a3][c1]>0&]},{\[Beta]0,V[a1,a2][b0]},{\[Beta]1,V[a0,b0][a6]},{\[Beta]2,V[b0,a3][c1]}]
]==0
,
{a0,A},{a1,B},{a2,C},{a3,D},{a5,fusionProduct[a0,a1]},{a6,fusionProduct[a5,a2]},{a4,fusionProduct[a6,a3]},{c0,fusionProduct[a2,a3]},{c1,Select[fusionProduct[a1,c0],V[a0,#][a4]>0&]},
{\[Alpha]0,V[a0,a1][a5]},{\[Alpha]1,V[a5,a2][a6]},{\[Alpha]2,V[a6,a3][a4]},{\[Gamma]0,V[a2,a3][c0]},{\[Gamma]1,V[a1,c0][c1]},{\[Gamma]2,V[a0,c1][a4]}
]]//DeleteDuplicates)

pentagonQ["C"|0]:=pentagonQ[obsC,obsC,obsC,obsC]
pentagonQ[1]:=pentagonQ[obsC,obsC,obsC,obsM]
pentagonQ[2,1]:=pentagonQ[obsC,obsC,obsM,obsD]
pentagonQ[2,2]:=pentagonQ[obsC,obsM,obsD,obsD]
pentagonQ[3]:=pentagonQ[obsM,obsD,obsD,obsD]
pentagonQ["D"|4]:=pentagonQ[obsD,obsD,obsD,obsD]


NpentagonQ[A_,B_,C_,D_]:={True}==(Flatten[Table[
Chop[
Sum[NF[a5,a2,a3][a4][\[Alpha]1,a6,\[Alpha]2][\[Gamma]0,c0,\[Delta]0]NF[a0,a1,c0][a4][\[Alpha]0,a5,\[Delta]0][\[Gamma]1,c1,\[Gamma]2],{\[Delta]0,V[a5,c0][a4]}]
-
Sum[NF[a0,a1,a2][a6][\[Alpha]0,a5,\[Alpha]1][\[Beta]0,b0,\[Beta]1]NF[a0,b0,a3][a4][\[Beta]1,a6,\[Alpha]2][\[Beta]2,c1,\[Gamma]2]NF[a1,a2,a3][c1][\[Beta]0,b0,\[Beta]2][\[Gamma]0,c0,\[Gamma]1],{b0,Select[fusionProduct[a1,a2],V[a0,#][a6]>0&&V[#,a3][c1]>0&]},{\[Beta]0,V[a1,a2][b0]},{\[Beta]1,V[a0,b0][a6]},{\[Beta]2,V[b0,a3][c1]}]
,10^-16]==0
,
{a0,A},{a1,B},{a2,C},{a3,D},{a5,fusionProduct[a0,a1]},{a6,fusionProduct[a5,a2]},{a4,fusionProduct[a6,a3]},{c0,fusionProduct[a2,a3]},{c1,Select[fusionProduct[a1,c0],V[a0,#][a4]>0&]},
{\[Alpha]0,V[a0,a1][a5]},{\[Alpha]1,V[a5,a2][a6]},{\[Alpha]2,V[a6,a3][a4]},{\[Gamma]0,V[a2,a3][c0]},{\[Gamma]1,V[a1,c0][c1]},{\[Gamma]2,V[a0,c1][a4]}
]]//DeleteDuplicates)

NpentagonQ["C"|0]:=NpentagonQ[obsC,obsC,obsC,obsC]
NpentagonQ[1]:=NpentagonQ[obsC,obsC,obsC,obsM]
NpentagonQ[2,1]:=NpentagonQ[obsC,obsC,obsM,obsD]
NpentagonQ[2,2]:=NpentagonQ[obsC,obsM,obsD,obsD]
NpentagonQ[3]:=NpentagonQ[obsM,obsD,obsD,obsD]
NpentagonQ["D"|4]:=NpentagonQ[obsD,obsD,obsD,obsD]


(* ::Section::Closed:: *)
(*Unitarity*)


uF1[a_,b_,c_][d_]:=
Table[
Sum[F[a,b,c][d][\[Alpha]0,e0,\[Beta]0][\[Sigma]0,f,\[Tau]0]Conjugate[F[a,b,c][d][\[Alpha]0p,e1,\[Beta]0p][\[Sigma]0,f,\[Tau]0]],{f,Select[fusionProduct[b,c],V[a,#][d]>0&]},{\[Sigma]0,V[b,c][f]},{\[Tau]0,V[a,f][d]}]-If[e0===e1&&\[Alpha]0===\[Alpha]0p&&\[Beta]0===\[Beta]0p,1,0]
,{e0,fusionProduct[a,b]},{e1,fusionProduct[a,b]},{\[Alpha]0,V[a,b][e0]},{\[Beta]0,V[e0,c][d]},{\[Alpha]0p,V[a,b][e1]},{\[Beta]0p,V[e1,c][d]}]

uF2[a_,b_,c_][d_]:=
Table[
Sum[F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0,f0,\[Tau]0]Conjugate[F[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0p,f1,\[Tau]0p]],{e,Select[fusionProduct[a,b],V[#,c][d]>0&]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]}]-If[f0===f1&&\[Sigma]0===\[Sigma]0p&&\[Tau]0===\[Tau]0p,1,0]
,{f0,fusionProduct[b,c]},{f1,fusionProduct[b,c]},{\[Sigma]0,V[b,c][f0]},{\[Tau]0,V[a,f0][d]},{\[Sigma]0p,V[b,c][f1]},{\[Tau]0p,V[a,f1][d]}]

unitaryQ[A_,B_,C_]:={True}==Module[{X},
Flatten[Table[
X=Flatten[{uF1[a,b,c][d],uF2[a,b,c][d]}];
RootReduce[X==ConstantArray[0,Dimensions[X]]]
,{a,A},{b,B},{c,C},{d,DeleteDuplicates[Flatten[fusionProduct[#,c]&/@fusionProduct[a,b]]]}]]//DeleteDuplicates
]

chkUnit[A_,B_,C_]:=Module[{X},
Flatten[Table[
X=Flatten[{uF1[a,b,c][d],uF2[a,b,c][d]}];
X
,{a,A},{b,B},{c,C},{d,DeleteDuplicates[Flatten[fusionProduct[#,c]&/@fusionProduct[a,b]]]}]]//DeleteDuplicates
]

chkUnit["C"|0]:=chkUnit[obsC,obsC,obsC]
chkUnit["L"|1]:=chkUnit[obsC,obsC,obsM]
chkUnit["\[CapitalOmega]"|2]:=chkUnit[obsC,obsM,obsD]
chkUnit["R"|3]:=chkUnit[obsM,obsD,obsD]
chkUnit["D"|4]:=chkUnit[obsD,obsD,obsD]

unitaryQ["C"|0]:=unitaryQ[obsC,obsC,obsC]
unitaryQ["L"|1]:=unitaryQ[obsC,obsC,obsM]
unitaryQ["\[CapitalOmega]"|2]:=unitaryQ[obsC,obsM,obsD]
unitaryQ["R"|3]:=unitaryQ[obsM,obsD,obsD]
unitaryQ["D"|4]:=unitaryQ[obsD,obsD,obsD]

NuF1[a_,b_,c_][d_]:=
Table[
Chop[Sum[NF[a,b,c][d][\[Alpha]0,e0,\[Beta]0][\[Sigma]0,f,\[Tau]0]Conjugate[NF[a,b,c][d][\[Alpha]0p,e1,\[Beta]0p][\[Sigma]0,f,\[Tau]0]],{f,Select[fusionProduct[b,c],V[a,#][d]>0&]},{\[Sigma]0,V[b,c][f]},{\[Tau]0,V[a,f][d]}]-If[e0===e1&&\[Alpha]0===\[Alpha]0p&&\[Beta]0===\[Beta]0p,1,0],10^-16]
,{e0,fusionProduct[a,b]},{e1,fusionProduct[a,b]},{\[Alpha]0,V[a,b][e0]},{\[Beta]0,V[e0,c][d]},{\[Alpha]0p,V[a,b][e1]},{\[Beta]0p,V[e1,c][d]}]

NuF2[a_,b_,c_][d_]:=
Table[
Chop[Sum[NF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0,f0,\[Tau]0]Conjugate[NF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Sigma]0p,f1,\[Tau]0p]],{e,Select[fusionProduct[a,b],V[#,c][d]>0&]},{\[Alpha]0,V[a,b][e]},{\[Beta]0,V[e,c][d]}]-If[f0===f1&&\[Sigma]0===\[Sigma]0p&&\[Tau]0===\[Tau]0p,1,0],10^-16]
,{f0,fusionProduct[b,c]},{f1,fusionProduct[b,c]},{\[Sigma]0,V[b,c][f0]},{\[Tau]0,V[a,f0][d]},{\[Sigma]0p,V[b,c][f1]},{\[Tau]0p,V[a,f1][d]}]

NunitaryQ[A_,B_,C_]:={True}==Module[{X},
Flatten[Table[
X=Flatten[{NuF1[a,b,c][d],NuF2[a,b,c][d]}];
RootReduce[X==ConstantArray[0,Dimensions[X]]]
,{a,A},{b,B},{c,C},{d,DeleteDuplicates[Flatten[fusionProduct[#,c]&/@fusionProduct[a,b]]]}]]//DeleteDuplicates
]

NunitaryQ["C"|0]:=NunitaryQ[obsC,obsC,obsC]
NunitaryQ["L"|1]:=NunitaryQ[obsC,obsC,obsM]
NunitaryQ["\[CapitalOmega]"|2]:=NunitaryQ[obsC,obsM,obsD]
NunitaryQ["R"|3]:=NunitaryQ[obsM,obsD,obsD]
NunitaryQ["D"|4]:=NunitaryQ[obsD,obsD,obsD]


(* ::Section::Closed:: *)
(*Tube Algebra*)


tube[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]/;(\[Alpha]0<=V[x,m][p]&&\[Beta]0<=V[x,n][q]):=tub[m,n][p,q][\[Alpha]0,x,\[Beta]0];
tube[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]:=0;

tubes[m_,n_][p_,q_]:=DeleteCases[Flatten[Table[tube[m,n][p,q][\[Alpha]0,x,\[Beta]0],{x,obsC},{\[Alpha]0,V[x,m][p]},{\[Beta]0,V[x,n][q]}]],0]

pictureBasis[]:=pictureBasis[]=DeleteDuplicates[Flatten[Table[tubes[m,n][p,q],{m,obsM},{n,obsM},{p,obsM},{q,obsM}]]];


mult[A_,B_]:=mult[A,B]=mult$[A,B]

mult$[tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_],tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=mult$[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]=If[(p===mp&&q===np),Sum[Sqrt[(dim[x]dim[xp])/dim[y]]Conjugate[F[xp,x,n][qp][\[Zeta]0,y,\[Tau]0][\[Beta]0,q,\[Beta]0p]]F[xp,x,m][pp][\[Zeta]0,y,\[Sigma]0][\[Alpha]0,p,\[Alpha]0p]tub[m,n][pp,qp][\[Sigma]0,y,\[Tau]0]
,{y,Select[fusionProduct[xp,x],V[#,n][qp]>0&&V[#,m][pp]>0&]},{\[Sigma]0,V[y,m][pp]},{\[Tau]0,V[y,n][qp]},{\[Zeta]0,V[xp,x][y]}],0]

mult$[\[Alpha]0_ A_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 mult$[A,B]
mult$[A_,\[Alpha]0_ B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 mult$[A,B]
mult$[A_+B_,C_]:=mult$[A,C]+mult$[B,C]
mult$[A_,B_+C_]:=mult$[A,B]+mult$[A,C]

mult$[\[Alpha]0_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 B
mult$[A_,\[Alpha]0_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 A

idtube:=Sum[tube[m,n][m,n][1,unitC,1],{m,obsM},{n,obsM}];

Nmult[tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_],tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=Nmult[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]=If[(p===mp&&q===np),Sum[Sqrt[(dim[x]dim[xp])/dim[y]]Conjugate[NF[xp,x,n][qp][\[Zeta]0,y,\[Tau]0][\[Beta]0,q,\[Beta]0p]]NF[xp,x,m][pp][\[Zeta]0,y,\[Sigma]0][\[Alpha]0,p,\[Alpha]0p]tub[m,n][pp,qp][\[Sigma]0,y,\[Tau]0]
,{y,Select[fusionProduct[xp,x],V[#,n][qp]>0&&V[#,m][pp]>0&]},{\[Sigma]0,V[y,m][pp]},{\[Tau]0,V[y,n][qp]},{\[Zeta]0,V[xp,x][y]}],0]

Nmult[\[Alpha]0_ A_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 Nmult[A,B]
Nmult[A_,\[Alpha]0_ B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 Nmult[A,B]
Nmult[A_+B_,C_]:=Nmult[A,C]+Nmult[B,C]
Nmult[A_,B_+C_]:=Nmult[A,B]+Nmult[A,C]

Nmult[\[Alpha]0_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 B
Nmult[A_,\[Alpha]0_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 A


star[A__]:=star[A]=star$[A]
star$[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=star$[tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]=Sum[dim[x]Sqrt[(dim[m]dim[n])/(dim[p]dim[q])]Conjugate[F[dual[x],x,m][m][1,unitC,1][\[Alpha]0,p,\[Sigma]0]]F[dual[x],x,n][n][1,unitC,1][\[Beta]0,q,\[Tau]0]tub[p,q][m,n][\[Sigma]0,dual[x],\[Tau]0],{\[Sigma]0,V[dual[x],p][m]},{\[Tau]0,V[dual[x],q][n]}](*//RootReduce*)
star$[\[Alpha]0_ A_]/;FreeQ[\[Alpha]0,tub]:=Conjugate[\[Alpha]0]star$[A]
star$[A_+B_]:=star$[A]+star$[B]
star$[\[Alpha]0_]/;FreeQ[\[Alpha]0,tub]:=Conjugate[\[Alpha]0]


tr[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=If[x===unitC,dim[m]dim[n],0]

tr[\[Alpha]0_ A_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 tr[A]
tr[A_+B_]:=tr[A]+tr[B]
tr[\[Alpha]0_ ]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0


dot[tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_],tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=dot[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]=tr[mult[star[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]]//ExpandAll//RootReduce
dot[\[Alpha]0_ A_,B_]/;FreeQ[\[Alpha]0,tub]:=Conjugate[\[Alpha]0]dot[A,B]
dot[A_,\[Alpha]0_ B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 dot[A,B]

dot[\[Alpha]0_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 B
dot[A_,\[Alpha]0_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 star[A]

dot[\[Alpha]0_,\[Beta]0_]/;FreeQ[\[Alpha]0,tub]&&FreeQ[\[Beta]0,tub]:=Conjugate[\[Alpha]0]\[Beta]0

dot[A_+B_,C_]:=dot[A,C]+dot[B,C]
dot[A_,B_+C_]:=dot[A,B]+dot[A,C]

norm[a_]:=norm[a]=Sqrt[dot[a,a]]

Ndot[tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_],tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_]]:=Ndot[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]=tr[Nmult[star[tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]]//RootReduce
Ndot[\[Alpha]0_ A_,B_]/;FreeQ[\[Alpha]0,tub]:=Conjugate[\[Alpha]0]Ndot[A,B]
Ndot[A_,\[Alpha]0_ B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 Ndot[A,B]

Ndot[\[Alpha]0_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 B
Ndot[A_,\[Alpha]0_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 star[A]

Ndot[\[Alpha]0_,\[Beta]0_]/;FreeQ[\[Alpha]0,tub]&&FreeQ[\[Beta]0,tub]:=Conjugate[\[Alpha]0]\[Beta]0

Ndot[A_+B_,C_]:=Ndot[A,C]+Ndot[B,C]
Ndot[A_,B_+C_]:=Ndot[A,B]+Ndot[A,C]


tubVars[X_]:=Cases[Variables[X],_?(!FreeQ[#,tub]&)];
toVec[X_]:=Coefficient[X,tubVars[X]]//RootReduce;

toNum[X_]:=Module[{basis=tubVars[X]},N[toVec[X],20] . basis]

clean[X_]:=Block[{Y=X},
Y=Collect[Y,tubVars[Y],RootReduce@*Simplify];
Return[Y]
];

multclean[i_,j_]:=multclean[i,j]=(clean@*mult)[i,j]


(*e[r_][i_,j_]/;(j>i):=e[r][i,j]=star[e[r][j,i]]//RootReduce//Simplify
e[r_][i_,j_]/;(0<=j<=i<dimRep[r]):=e[r][i,j]=multclean[e[r][i,0],e[r][0,j]]*)


(* ::Section::Closed:: *)
(*Tensor product *)


compose[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_],tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_]]:=If[q===pp,TensorProduct[tub[m,n][p,q][\[Alpha]0,x,\[Beta]0],tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]],0]

compose[\[Alpha]0_ A_,B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 compose[A,B]
compose[A_,\[Alpha]0_ B_]/;FreeQ[\[Alpha]0,tub]:=\[Alpha]0 compose[A,B]
compose[A_+B_,C_]:=compose[A,C]+compose[B,C]
compose[A_,B_+C_]:=compose[A,B]+compose[A,C]


mult$[tub[mpp_,npp_][ppp_,qpp_][\[Alpha]0pp_,xpp_,\[Beta]0pp_],TensorProduct[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_],tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_]]]:=
mult$[tub[mpp,npp][ppp,qpp][\[Alpha]0pp,xpp,\[Beta]0pp],TensorProduct[tub[m,n][p,q][\[Alpha]0,x,\[Beta]0],tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]]]=(If[p===mpp&&qp===npp,Sum[
Sqrt[(dim[r]dim[x]dim[xpp]dim[xp]dim[xpp])/(dim[xpp]dim[q]dim[y]dim[yp])]
Conjugate[F[xpp,x,n][r][\[Zeta]1,y,\[Tau]0][\[Beta]0,q,\[Zeta]0]]
F[xpp,x,m][ppp][\[Zeta]1,y,\[Sigma]0][\[Alpha]0,p,\[Alpha]0pp]
Conjugate[F[xpp,xp,np][qpp][\[Zeta]2,yp,\[Tau]0p][\[Beta]0p,qp,\[Beta]0pp]]
F[xpp,xp,mp][r][\[Zeta]2,yp,\[Sigma]0p][\[Alpha]0p,q,\[Zeta]0]
TensorProduct[tub[m,n][ppp,r][\[Sigma]0,y,\[Tau]0],tub[mp,np][r,qpp][\[Sigma]0p,yp,\[Tau]0p]],
{r,fusionProduct[xpp,q]},{y,Select[fusionProduct[xpp,x],V[#,n][r]>0&&V[#,m][ppp]>0&]},{yp,Select[fusionProduct[xpp,xp],V[#,np][qpp]>0&&V[#,mp][r]>0&]},
{\[Zeta]0,V[xpp,q][r]},{\[Zeta]1,V[xpp,x][y]},{\[Zeta]2,V[xpp,xp][yp]},{\[Sigma]0,V[y,m][ppp]},{\[Sigma]0p,V[yp,mp][r]},{\[Tau]0,V[y,n][r]},{\[Tau]0p,V[yp,np][qpp]}]
,0]
)

Nmult[tub[mpp_,npp_][ppp_,qpp_][\[Alpha]0pp_,xpp_,\[Beta]0pp_],TensorProduct[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_],tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_]]]:=
Nmult[tub[mpp,npp][ppp,qpp][\[Alpha]0pp,xpp,\[Beta]0pp],TensorProduct[tub[m,n][p,q][\[Alpha]0,x,\[Beta]0],tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]]]=(If[p===mpp&&qp===npp,Sum[
Sqrt[(dim[r]dim[x]dim[xpp]dim[xp]dim[xpp])/(dim[xpp]dim[q]dim[y]dim[yp])]
Conjugate[NF[xpp,x,n][r][\[Zeta]1,y,\[Tau]0][\[Beta]0,q,\[Zeta]0]]
NF[xpp,x,m][ppp][\[Zeta]1,y,\[Sigma]0][\[Alpha]0,p,\[Alpha]0pp]
Conjugate[NF[xpp,xp,np][qpp][\[Zeta]2,yp,\[Tau]0p][\[Beta]0p,qp,\[Beta]0pp]]
NF[xpp,xp,mp][r][\[Zeta]2,yp,\[Sigma]0p][\[Alpha]0p,q,\[Zeta]0]
TensorProduct[tub[m,n][ppp,r][\[Sigma]0,y,\[Tau]0],tub[mp,np][r,qpp][\[Sigma]0p,yp,\[Tau]0p]],
{r,fusionProduct[xpp,q]},{y,Select[fusionProduct[xpp,x],V[#,n][r]>0&&V[#,m][ppp]>0&]},{yp,Select[fusionProduct[xpp,xp],V[#,np][qpp]>0&&V[#,mp][r]>0&]},
{\[Zeta]0,V[xpp,q][r]},{\[Zeta]1,V[xpp,x][y]},{\[Zeta]2,V[xpp,xp][yp]},{\[Sigma]0,V[y,m][ppp]},{\[Sigma]0p,V[yp,mp][r]},{\[Tau]0,V[y,n][r]},{\[Tau]0p,V[yp,np][qpp]}]
,0]
)


dot[TensorProduct[tub[r_,s_][t_,u_][\[Sigma]0_,y_,\[Tau]0_],tub[rp_,sp_][tp_,up_][\[Sigma]0p_,yp_,\[Tau]0p_]],TensorProduct[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_],tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_]]]:=(dot[tub[r,s][t,u][\[Sigma]0,y,\[Tau]0],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]dot[tub[rp,sp][tp,up][\[Sigma]0p,yp,\[Tau]0p],tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]])/Sqrt[dim[q]dim[u]]

Ndot[TensorProduct[tub[r_,s_][t_,u_][\[Sigma]0_,y_,\[Tau]0_],tub[rp_,sp_][tp_,up_][\[Sigma]0p_,yp_,\[Tau]0p_]],TensorProduct[tub[m_,n_][p_,q_][\[Alpha]0_,x_,\[Beta]0_],tub[mp_,np_][pp_,qp_][\[Alpha]0p_,xp_,\[Beta]0p_]]]:=(Ndot[tub[r,s][t,u][\[Sigma]0,y,\[Tau]0],tub[m,n][p,q][\[Alpha]0,x,\[Beta]0]]Ndot[tub[rp,sp][tp,up][\[Sigma]0p,yp,\[Tau]0p],tub[mp,np][pp,qp][\[Alpha]0p,xp,\[Beta]0p]])/Sqrt[dim[q]dim[u]]


V[r1_,r2_][r3_]/;ContainsAll[obsD,{r1,r2,r3}]:=V[r1,r2][r3]=Module[{basis=tensorRepBasis[r1,r2],d,T=Variables[tensorRepBasis[r1,r2]],M={},vi,x},
d=Length[basis];
While[
vi=basis . RandomComplex[{-(1+I)/Sqrt[2],(1+I)/Sqrt[2]},d]//Simplify;(*Pick a random vector in r1\[CircleTimes]0r2*)
x=(Chop@*Coefficient)[mult[e[r3][0,0],vi],T];(*Project onto rep r3, compute the associated column vector in the picture basis*)
If[M=={},M={x};True,MatrixRank[M]<MatrixRank[AppendTo[M,x]]](*If the new vector is linearly indep, continue*)
];
Return[MatrixRank[M]]
]


v[r_][i_]/;MemberQ[obsD,r]&&i<dimRep[r]:=v[r][i]=clean[e[r][i,0]/norm[e[r][i,0]]]
v[x_,y_][i_,j_]:=v[x,y][i,j]=(clean@*compose)[v[x][i],v[y][j]]

repBasis[r_]/;MemberQ[obsD,r]:=(v[r][#]&/@Range[0,dimRep[r]-1])

tensorRepBasis[x_,y_]:=tensorRepBasis[x,y]=DeleteCases[DeleteDuplicates[Flatten[Table[
Block[{x0=(clean@*compose)[v0,v1],nx},
If[norm[x0]!=0,x0/norm[x0],0]
]
,{v0,repBasis[x]},{v1,repBasis[y]}]]],0](*Note, this basis may be overcomplete. That won't matter for our purposes*)


VEmbedding[C0_->A0_\[CircleTimes]B0_]/;MemberQ[fusionProduct[A0,B0],C0]:=VEmbedding[C0->A0\[CircleTimes]B0]=Module[
{dimAB,basisAB=tensorRepBasis[A0,B0],X,v0,vi,v0s,\[Alpha],T,ri,x},
dimAB=Length[basisAB];
ri[]:=If[x=RandomInteger[{-5Length[basisAB],5Length[basisAB]}];x==0,ri[],x];

X=Table[ri[],{i,V[A0,B0][C0]},{b,dimAB}];
If[V[A0,B0][C0]==1,
v0s=mult[e[C0][0,0],#]&/@(X . basisAB);v0s=clean[#/norm[#]]&/@v0s;
,
v0s=Orthogonalize[mult[e[C0][0,0],#]&/@(X . basisAB),(dot)];
];

Do[
v0=v0s[[k]];
T[k]={coeff[v0,basisAB]//RootReduce};
Do[
vi=coeff[multclean[e[C0][i,0],v0],basisAB]//RootReduce;
AppendTo[T[k],vi],{i,dimRep[C0]-1}
];
,{k,V[A0,B0][C0]}
];

Return[T];
]
VEmbedding[C0_->A0_\[CircleTimes]B0_,\[Mu]0_]/;(\[Mu]0<=V[A0,B0][C0]):=VEmbedding[C0->A0\[CircleTimes]B0,\[Mu]0]=Transpose[VEmbedding[C0->A0\[CircleTimes]B0][\[Mu]0]]


embed[\[Alpha]0_,\[Beta]0_]:=embed[\[Alpha]0,\[Beta]0]=Module[{a,b,r=1,c=1,x,M=ConstantArray[0,{dimRep[\[Alpha]0]dimRep[\[Beta]0],Length[tensorRepBasis[\[Alpha]0,\[Beta]0]]}]},
Do[
If[(clean@*compose)[v[\[Alpha]0][a],v[\[Beta]0][b]]===0,
r++
,
M[[r,c]]=1;
r++;c++
];
,{a,0,dimRep[\[Alpha]0]-1},{b,0,dimRep[\[Beta]0]-1}];
Return[ArrayReshape[M,{dimRep[\[Alpha]0],dimRep[\[Beta]0],Length[tensorRepBasis[\[Alpha]0,\[Beta]0]]}]]
]

VEmbeddingFull[\[Gamma]0_->\[Alpha]0_\[CircleTimes]\[Beta]0_,x_]/;(MemberQ[fusionProduct[\[Alpha]0,\[Beta]0],\[Gamma]0]&&x<=V[\[Alpha]0,\[Beta]0][\[Gamma]0]):=VEmbeddingFull[\[Gamma]0->\[Alpha]0\[CircleTimes]\[Beta]0,x]=embed[\[Alpha]0,\[Beta]0] . VEmbedding[\[Gamma]0->\[Alpha]0\[CircleTimes]\[Beta]0,x]

leftTree[\[Alpha]0_,\[Beta]0_,\[Gamma]0_][\[Delta]0_][i_,\[Sigma]0_,j_]:=VEmbeddingFull[\[Sigma]0->\[Alpha]0\[CircleTimes]\[Beta]0,i] . VEmbeddingFull[\[Delta]0->\[Sigma]0\[CircleTimes]\[Gamma]0,j]
rightTree[\[Alpha]0_,\[Beta]0_,\[Gamma]0_][\[Delta]0_][k_,\[Tau]0_,l_]:=TensorTranspose[VEmbeddingFull[\[Tau]0->\[Beta]0\[CircleTimes]\[Gamma]0,k] . TensorTranspose[VEmbeddingFull[\[Delta]0->\[Alpha]0\[CircleTimes]\[Tau]0,l],{2,1,3}],{2,3,1,4}]


solveForF[\[Alpha]0_,\[Beta]0_,\[Gamma]0_][\[Delta]0_]:=solveForF[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0]=Module[{A,B,sol,i,j,lB=leftBasis[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],rB=rightBasis[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],l,r},
A=Table[Flatten[leftTree[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][l[[1]],l[[2]],l[[3]]]],{l,lB}];
B=Table[Flatten[rightTree[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][r[[1]],r[[2]],r[[3]]]],{r,rB}];
sol=Transpose[LinearSolve[Transpose[B],Transpose[A]]]//Simplify//RootReduce;
Flatten[Table[X0[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][lB[[i,1]],lB[[i,2]],lB[[i,3]]][rB[[j,1]],rB[[j,2]],rB[[j,3]]]->sol[[i,j]],{i,Length[lB]},{j,Length[rB]}]]
]


FData[4]:=FData[4]=Table[solveForF[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],{\[Alpha]0,obsD},{\[Beta]0,obsD},{\[Gamma]0,obsD},{\[Delta]0,Intersection[Flatten[(fusionProduct[#,\[Gamma]0]&/@fusionProduct[\[Alpha]0,\[Beta]0])],Flatten[(fusionProduct[\[Alpha]0,#]&/@fusionProduct[\[Beta]0,\[Gamma]0])]]}]//Flatten


NF[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]/;MemberQ[obsD,a]&&MemberQ[obsD,b]&&MemberQ[obsD,c]&&MemberQ[fusionProduct[a,b],e]&&MemberQ[fusionProduct[b,c],f]&&MemberQ[Intersection[fusionProduct[e,c],fusionProduct[a,f]],d]&&\[Alpha]0<=V[a,b][e]&&\[Beta]0<=V[e,c][d]&&\[Mu]0<=V[b,c][f]&&\[Nu]0<=V[a,f][d]:=NF[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=
X0[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]//.NFData[4]

NFData[4]:=NFData[4]=Table[NsolveForF[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],{\[Alpha]0,obsD},{\[Beta]0,obsD},{\[Gamma]0,obsD},{\[Delta]0,Intersection[Flatten[(fusionProduct[#,\[Gamma]0]&/@fusionProduct[\[Alpha]0,\[Beta]0])],Flatten[(fusionProduct[\[Alpha]0,#]&/@fusionProduct[\[Beta]0,\[Gamma]0])]]}]//Flatten


NsolveForF[\[Alpha]0_,\[Beta]0_,\[Gamma]0_][\[Delta]0_]:=NsolveForF[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0]=Module[{A,B,sol,i,j,lB=leftBasis[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],rB=rightBasis[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0],l,r},
A=N[Table[Flatten[leftTree[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][l[[1]],l[[2]],l[[3]]]],{l,lB}],20];
B=N[Table[Flatten[rightTree[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][r[[1]],r[[2]],r[[3]]]],{r,rB}],20];
sol=Transpose[LinearSolve[Transpose[B],Transpose[A]]]//RootReduce;
Flatten[Table[X0[\[Alpha]0,\[Beta]0,\[Gamma]0][\[Delta]0][lB[[i,1]],lB[[i,2]],lB[[i,3]]][rB[[j,1]],rB[[j,2]],rB[[j,3]]]->sol[[i,j]],{i,Length[lB]},{j,Length[rB]}]]
]


isometricQ:=isometricQ=DeleteDuplicates[Flatten[Table[
RootReduce[KroneckerDelta[x,y](dot)[v[\[Gamma]0][i],v[\[Gamma]0][j]]
==
RootReduce[(dot)[VEmbedding[\[Gamma]0->\[Alpha]0\[CircleTimes]\[Beta]0,x][[;;,i+1]] . tensorRepBasis[\[Alpha]0,\[Beta]0],VEmbedding[\[Gamma]0->\[Alpha]0\[CircleTimes]\[Beta]0,y][[;;,j+1]] . tensorRepBasis[\[Alpha]0,\[Beta]0]]]]
,
{\[Alpha]0,obsD},{\[Beta]0,obsD},{\[Gamma]0,fusionProduct[\[Alpha]0,\[Beta]0]},{i,0,dimRep[\[Gamma]0]-1},{j,0,dimRep[\[Gamma]0]-1},{x,V[\[Alpha]0,\[Beta]0][\[Gamma]0]},{y,V[\[Alpha]0,\[Beta]0][\[Gamma]0]}
]]]


(* ::Section::Closed:: *)
(*2F*)


dotBasis[c_][m_,n_]:=dotBasis[c][m,n]=Select[repBasis[c],List@@Variables[#][[1,0]]=={m,n}&]
dotBasisVector[c_][m_,n_][\[Alpha]0_]/;MemberQ[obsD,c]&&\[Alpha]0<=V[m,c][n]:=dotBasis[c][m,n][[\[Alpha]0]]

V[a_,b_][c_]/;ContainsAll[obsM,{a,c}]&&MemberQ[obsD,b]:=V[a,b][c]=Length[dotBasis[b][a,c]]

X02[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:=X02[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=RootReduce[1/Sqrt[dim[a]] ((dim[e]dim[f])/(dim[b]dim[d]))^(1/4) dot[mult[tub[b,f][e,d][\[Alpha]0,a,\[Nu]0],dotBasisVector[c][b,f][\[Mu]0]],dotBasisVector[c][e,d][\[Beta]0]]];
FData[2]:=Fdata[2]={X0[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:>X02[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]}


(* ::Section::Closed:: *)
(*3F*)


X03[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:=X03[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]=RootReduce[Simplify[Conjugate[coeff[compose[dotBasisVector[b][a,e][\[Alpha]0],dotBasisVector[c][e,d][\[Beta]0]]/norm[compose[dotBasisVector[b][a,e][\[Alpha]0],dotBasisVector[c][e,d][\[Beta]0]]],tensorRepBasis[b,c]] . VEmbedding[f->b\[CircleTimes]c,\[Mu]0] . coeff[dotBasisVector[f][a,d][\[Nu]0]/norm[dotBasisVector[f][a,d][\[Nu]0]],repBasis[f]]]]]; 
FData[3]:={X0[a_,b_,c_][d_][\[Alpha]0_,e_,\[Beta]0_][\[Mu]0_,f_,\[Nu]0_]:>X03[a,b,c][d][\[Alpha]0,e,\[Beta]0][\[Mu]0,f,\[Nu]0]}
