(* ::Package:: *)

buildVecG[G$_]:=Module[
{GEls=GroupElements[G$]},

obsC=obC[#]&/@Range[0,GroupOrder[G$]-1];
V[obC[a_],obC[b_]][obC[c_]]:=V[obC[a],obC[b]][obC[c]]=If[GEls[[a+1]]\[PermutationProduct]GEls[[b+1]]==GEls[[c+1]],1,0];

objNames[obC[x_]]:=objNames[obC[x]]=Module[
{w=GroupElementToWord[G$,GEls[[x+1]]],n,name,f,gens=GroupGenerators[G$]},
If[Length[w]==0,Return[1]];
f[q_]:=If[q>0,Subscript[\[Sigma], q],Power[Subscript[\[Sigma], Abs[q]],PermutationOrder[gens[[Abs[q]]]]-1]];

name=PermutationProduct@@(f[#]&/@w);
Return[name]
];

FData[0]={X0[a_,b_,c_][d_][1,e_,1][1,f_,1]:>1};
]


buildM[G$_,H$_]:=Module[
{GEls=GroupElements[G$],cosets,cosetRepresentatives},

Print["Computing module action"];

cosets=Sort[#]&/@Gather[GEls,GroupElementQ[H$,PermutationProduct[InversePermutation[#1],#2]]&];
cosetRepresentatives=First[#]&/@cosets;

obsM=obM[#]&/@Range[0,Length[cosets]-1];

V[obC[a_],obM[b_]][obM[c_]]:=V[obC[a],obM[b]][obM[c]]=If[GroupElementQ[H$,InversePermutation[cosetRepresentatives[[c+1]]]\[PermutationProduct]GEls[[a+1]]\[PermutationProduct]cosetRepresentatives[[b+1]]],1,0];

objNames[obM[x_]]:=objNames[obM[x]]=Module[
{gname,name},
gname=objNames[obC[Position[GEls,cosets[[x+1,1]]][[1,1]]-1]];
If[gname===1,name="H",name=gname\[PermutationProduct]"H"];
Return[name]
];
FData[1]={X0[a_,b_,c_][d_][1,e_,1][1,f_,1]:>1};
]


multclean[a_,b_,c__]:=multclean[multclean[a,b],c]
multclean[a_]:=a

idempotents[m_,n_]:=Module[
{bs=tubes[m,n][m,n],v$,M,x,w,unit,ids,b,ri},
unit=tube[m,n][m,n][1,unitC,1];

ri[]:=If[x=(RandomInteger[{-5Length[bs],5Length[bs]}]+I RandomInteger[{-5Length[bs],5Length[bs]}]);x==0,ri[],x];

v$=Total[ri[]#&/@bs];
(*v$=v$+star[v$];*)
M=Transpose[(coeff[multclean[v$,#],bs]&/@bs)];
x=DeleteDuplicates[Eigenvalues[M]];

If[Length[x]==1,
ids={v$};
,
b[\[Lambda]_]:=multclean@@Collect[v$-# unit&/@DeleteCases[x,\[Lambda]],bs,Simplify];
ids=b[#]&/@x;
];

Do[
M=Transpose[(coeff[multclean[ids[[i]],#],bs]&/@bs)];
ids[[i]]=ids[[i]]/Eigenvalues[M][[1]];
,{i,1,Length[ids]}];

Return[ids//clean];
]

constructReps[]:=Module[
{eiis,irrs,gps,R,Flg,\[Alpha],j,M,nM,ri,x},

Print["Computing irreps"];

eiis=Table[
Quiet[
x=False;
While[x==False,
x=Check[idempotents[a,b],False];
]];x
,{a,obsM},{b,obsM}]//Flatten;

ri[]:=If[x=(RandomInteger[{-5Length[pictureBasis[]],5Length[pictureBasis[]]}]+I RandomInteger[{-5Length[pictureBasis[]],5Length[pictureBasis[]]}]);x==0,ri[],x];

R=Total[ri[]#&/@pictureBasis[]];
R=1/2 (R+star[R]);

irrs={
{eiis[[1]]}
};

Do[
Flg=False;


Do[
M=multclean[eiis[[j]],R,irrs[[\[Alpha],1]]];
nM=norm[Collect[M,pictureBasis[],N[#,20]&]];

If[norm[M]!=0,AppendTo[irrs[[\[Alpha]]],clean[M/norm[M] norm[irrs[[\[Alpha],1]]]]];Flg=True;Break[]];

,{\[Alpha],1,Length[irrs]}
];
If[!Flg,AppendTo[irrs,{eiis[[j]]}]];
,{j,2,Length[eiis]}];


obsD=obD[#]&/@Range[0,Length[irrs]-1];

objNames[obD[x_]]:=Subscript[\[DoubledPi], x];

(dimRep[obD[#]]=Length[irrs[[#+1]]])&/@Range[0,Length[irrs]-1];

Do[e[obD[\[Alpha]]][j,0]=irrs[[\[Alpha]+1]][[j+1]],{\[Alpha],0,Length[obsD]-1},{j,0,dimRep[obD[\[Alpha]]]-1}];

e[r_][i_,j_]/;(j>i):=e[r][i,j]=star[e[r][j,i]]//RootReduce//Simplify;
e[r_][i_,j_]/;(0<j<=i<dimRep[r]):=e[r][i,j]=multclean[e[r][i,0],e[r][0,j]];
]


goodMatrixUnitsQ[]:=Module[{S,T1,T2},
S=Total[#^2&/@(dimRep[#]&/@obsD)]==Length[pictureBasis[]];

T1=Table[
Table[
Quiet[Collect[mult[e[\[Alpha]][i,j],e[\[Beta]][k,l]]-If[j==k&&\[Alpha]===\[Beta],e[\[Alpha]][i,l],0],pictureBasis[],Chop[N[#]]&]==0]
,{i,0,dimRep[\[Alpha]]-1},{j,0,dimRep[\[Alpha]]-1},{k,0,dimRep[\[Beta]]-1},{l,0,dimRep[\[Beta]]-1}
],{\[Alpha],obsD},{\[Beta],obsD}]//Flatten//DeleteDuplicates;
Print["A"];
T2=Table[
clean[e[\[Alpha]][i,j]-star[e[\[Alpha]][j,i]]]==0
,{\[Alpha],obsD},{i,0,dimRep[\[Alpha]]-1},{j,0,dimRep[\[Alpha]]-1}]//FullSimplify//RootReduce//Flatten//DeleteDuplicates;
T1=={True}&&T2=={True}&&S
]


computeMoritaDual[G$_,H$_]:=computeMoritaDual[G$,H$,True]

computeMoritaDual[G$_,H$_,computeIntertwiners_]:=Module[{},
buildVecG[G];
buildM[G,H];
constructReps[];
(*Print["Verifying representations"];
Print["Good irreps: ",If[goodMatrixUnitsQ[],"\[Checkmark]","\:2717"]];*)
If[Length[obsM]==1,matrixRepresentations[G$]];

If[computeIntertwiners,
Print["Computing intertwiners"];
Monitor[
Do[VEmbedding[c->a\[CircleTimes]b,\[Mu]],{a,obsD},{b,obsD},{c,fusionProduct[a,b]},{\[Mu],V[a,b][c]}];
,ProgressIndicator[(Position[obsD,b][[1,1]]+(Position[obsD,a][[1,1]]-1)Length[obsD])/Length[obsD]^2]];
Print["Verifying isometric"];
Print["Isometric: ",If[isometricQ=={True},"\[Checkmark]","\:2717"]];
]
];

verifyData[]:=Module[{},
Print["Pentagons: ",If[pentagonQ[0]&&pentagonQ[1]&&pentagonQ[2,1]&&pentagonQ[2,2]&&pentagonQ[3]&&pentagonQ[4],"\[Checkmark]","\:2717"]];
Print["Unitary: ",If[unitaryQ[0]&&unitaryQ[1]&&unitaryQ[2]&&unitaryQ[3]&&unitaryQ[4],"\[Checkmark]","\:2717"]];

]


verifyInvertibility[]:=Module[{dimCrit,charCrit},

dimCrit=dtot["C"]==dtot["D"];

charCrit=1/Length[obsM] Table[
Sum[dim[a]/dim[b]^2 F[a,b,c][d][\[Alpha],b,\[Mu]][\[Mu],d,\[Beta]]Conjugate[F[a,b,c$][d][\[Alpha],b,\[Nu]][\[Nu],d,\[Beta]]],{a,obsC},{b,Select[obsM,V[a,#][#]>0&]},{d,Select[Intersection[fusionProduct[b,c],fusionProduct[b,c$]],V[a,#][#]>0&]},{\[Alpha],V[a,b][b]},{\[Beta],V[a,d][d]},{\[Mu],V[b,c][d]},{\[Nu],V[b,c$][d]}]

,{c,obsD},{c$,obsD}
]==IdentityMatrix[Length[obsD]]//RootReduce;
Print["Invertibility criteria: ",If[dimCrit&&charCrit,"\[Checkmark]","\:2717"]]
]


schurOrthogQ[]:=Print["Schur orthogonality: ",If[
(Table[
RootReduce@Simplify[Sum[dim[a]F[a,b,c][d][\[Alpha],e,\[Beta]][\[Mu],f,\[Nu]]Conjugate[F[a,b,c$][d][\[Alpha],e,\[Beta]$][\[Mu]$,f,\[Nu]]],{a,obsC},{\[Alpha],V[a,b][e]},{\[Nu],V[a,f][d]}]]-(dim[e]dim[f])/dim[c] KroneckerDelta[\[Beta],\[Beta]$]KroneckerDelta[\[Mu],\[Mu]$]If[c===c$,1,0]==0
,{b,obsM},{c,obsD},{c$,obsD},{e,obsM},{d,Intersection[fusionProduct[e,c],fusionProduct[e,c$]]},{f,Intersection[fusionProduct[b,c],fusionProduct[b,c$]]},{\[Beta],V[e,c][d]},{\[Beta]$,V[e,c$][d]},{\[Mu],V[b,c][f]},{\[Mu]$,V[b,c$][f]}
]//Flatten//DeleteDuplicates)=={True},"\[Checkmark]","\:2717"]]


matrixRepresentations[G$_]:=Module[{},
If[Length[obsM]==1,
Subscript[\[Rho], x_][g_]:=Module[{
bs=v[obD[x]][#]&/@Range[0,dimRep[obD[x]]-1]
},
Transpose[(coeff[
multclean[
tub[obM[0],obM[0]][obM[0],obM[0]][1,obC[Position[GroupElements[G$],g][[1,1]]-1],1],#
],bs
]&/@bs)]//FullSimplify
];

Subscript[\[Chi], x_][g_]:=Tr[Subscript[\[Rho], x][g]];

conjugacyClasses[G$$_]:=Sort[#]&/@GroupOrbits[G$$,GroupElements[G$$]];
conjugacyClassRepresentatives[G$$_]:=First[#]&/@conjugacyClasses[G$$];
]
]
