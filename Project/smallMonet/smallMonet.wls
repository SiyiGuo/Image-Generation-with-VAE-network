#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 64;
width = 256;
convChannel = 64;
kernel = 8;


convIN[args___]:={ConvolutionLayer[args],InstanceNormalizationLayer["Epsilon"->0.00001]}
convINlrelu[args___]:={ConvolutionLayer[args],InstanceNormalizationLayer["Epsilon"->0.00001],lrelu}
convINRamp[args___]:={ConvolutionLayer[args],InstanceNormalizationLayer["Epsilon"->0.00001],ElementwiseLayer[Ramp]}
residualModule=NetGraph[
{
NetChain@Join[{PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"]},convINRamp[128,3],{PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"]},convIN[128,3]],
TotalLayer[]
},
{NetPort["Input"]->{1,2},1->2}
];
lrelu = ElementwiseLayer[Max[Ramp[#], #*0.3]&];


encoder = NetChain[{
ReshapeLayer[{3,width,width}],
PaddingLayer[{{0,0},{3,3},{3,3}},"Padding"->"Reflected"],
convINlrelu[32,7],
PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"],
convINlrelu[64,3,"Stride"->2],
PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"],
convINlrelu[128,3,"Stride"->2],
ConstantArray[residualModule,4],
PaddingLayer[{{0,0},{3,3},{3,3}},"Padding"->"Reflected"],
convINlrelu[64,7],
PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"],
convINlrelu[32,3, "Stride"->2],
PaddingLayer[{{0,0},{1,1},{1,1}},"Padding"->"Reflected"],
convINlrelu[16,3, "Stride"->2],
FlattenLayer[],
2048,
lrelu,
512
}]

(*
ConvolutionLayer[128, 4, "Stride"->2, "PaddingSize"->1],
lrelu,
ConvolutionLayer[64, 2, "Stride"->2, "PaddingSize"->1],
lrelu,
ConvolutionLayer[32, 1, "Stride"->2, "PaddingSize"->1],
lrelu,
ConvolutionLayer[16, 1, "Stride"->2, "PaddingSize"->1],
lrelu,
ConvolutionLayer[8, 1, "Stride"->2, "PaddingSize"->1],
lrelu,
FlattenLayer[],
512
*)


mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];


decoder = NetChain[{
512,
lrelu,
2048,
lrelu,
4096,
lrelu,
ReshapeLayer[{16,16,16}],
DeconvolutionLayer[32, 2, "Stride"->2],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[64, 2, "Stride"->2],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[128, 2, "Stride"->2],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[256, 2, "Stride"->2],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[256, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[256, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[256, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[256, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[128, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[64, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[32, 1, "Stride"->1],
BatchNormalizationLayer[],
Ramp,
DeconvolutionLayer[3, 1, "Stride"->1],
LogisticSigmoid
}, "Input"->{nlatent}]

(*
decoder = NetChain[{
512,
lrelu,
2048,
lrelu,
ReshapeLayer[{8,16,16}],
DeconvolutionLayer[convChannel, {4,4}, "Stride"->2,"PaddingSize"->1],
Ramp,
DeconvolutionLayer[32, {4,4}, "Stride"->2,"PaddingSize"->1],
Ramp,
DeconvolutionLayer[16, {4,4}, "Stride"->2,"PaddingSize"->1],
Ramp,
DeconvolutionLayer[3, {4,4}, "Stride"->2,"PaddingSize"->1],
LogisticSigmoid
}, "Input"->{nlatent}]
*)


(*Assume input is {1,28,28}*)
(*output the real number as wll*)
imageLoss = NetGraph[
{ElementwiseLayer[-1*# &, "Input"->{3,width,width}], TotalLayer[], ElementwiseLayer[#^2&], SummationLayer[]},
{
NetPort["inDec"]->1->2,
NetPort["inInput"]->2,
2->3->4
}
];


latentLoss = NetGraph[
{ElementwiseLayer[-0.5*#&], TotalLayer[], ElementwiseLayer[-(#^2)&], ElementwiseLayer[-Exp[2*#]&], ElementwiseLayer[1+2*#&],SummationLayer[]},
{
NetPort["mn"]->3,
NetPort["sd"]->4,
NetPort["sd"]->5,
3->2,
4->2,
5->2,
2->6,
6->1
}
];


loss = ThreadingLayer[(#1+#2) / 2&, "Output"->"Real"];


vaeNet = NetInitialize[NetGraph[
<|"enc"->encoder,
"mn"->mn,
"sd"-> sd,"expSd"->expSd,"sdEpsilon"->ThreadingLayer[Times],
"z"->TotalLayer[],
"dec"->decoder,
"imageLoss"->imageLoss,
"latentLoss"->latentLoss,
"loss"->loss
|>,

{
NetPort["Input"]->"enc",
"enc"->"mn",
 "enc"->"sd", 
"sd"->"expSd","expSd"->"sdEpsilon", NetPort["random"] ->"sdEpsilon",
"mn"->"z", 
"sdEpsilon"->"z",
"z"->"dec",
"dec"->NetPort["Output"],
(*latent loss*)
"sd"->NetPort["latentLoss","sd"],
"mn"->NetPort["latentLoss","mn"],
(*image loss*)
"dec"->NetPort["imageLoss", "inDec"],
NetPort["Input"]->NetPort["imageLoss", "inInput"],
(*Total loss8*)
"latentLoss"->NetPort["loss", "1"],
"imageLoss"->NetPort["loss", "2"],
"loss"->NetPort["MeanLoss"]
},
"Output"->NetDecoder[{"Image", "RGB"}],
"Input"->NetEncoder[{"Image", {width, width}, "RGB"}]
]]


imagePaths = Join[
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg",FileNameJoin[{NotebookDirectory[],"DataMonet"}]]],
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg",FileNameJoin[{NotebookDirectory[],"DataVanGh"}]]],
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg",FileNameJoin[{NotebookDirectory[],"DataLandScape"}]]],
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg",FileNameJoin[{NotebookDirectory[],"DataCezanne"}]]]
];
dataSets = Map[Import[#]&, imagePaths];
trainingData =<|"random"->RandomVariate[NormalDistribution[],{Length@dataSets,nlatent}],
"Input"->dataSets|>;
Echo[Length@dataSets];


dir = CreateDirectory[]


(*vaeNet*)
SetDirectory[NotebookDirectory[]]
trainedVae = NetTrain[vaeNet, trainingData, LossFunction->{"MeanLoss"->Scaled[1]},
MaxTrainingRounds->2000,
TrainingProgressReporting->"Panel",
Method->{"ADAM", "LearningRate"->0.0005},
TrainingProgressCheckpointing->{"Directory", dir, "Interval"->Quantity[50, "Rounds"]},
TargetDevice->"GPU",
 BatchSize->16]
 Export["smallMonet.wlnet", vaeNet]






decd = NetExtract[trainedVae, "dec"]
initial = RandomVariate[NormalDistribution[], {16,64}];
b = NetDecoder[{"Image", "RGB"}]
Magnify[b[decd[initial]], 2]






