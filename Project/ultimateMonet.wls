#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 64;
width = 256;
convChannel = 64;
kernel = 8;


convIN[args___]:={ConvolutionLayer[args]}
convINlrelu[args___]:={ConvolutionLayer[args]Tanh}
convINRamp[args___]:={ConvolutionLayer[args],Tanh}
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


mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];


decoder = NetChain[{
512,
lrelu,
2048,
Tanh,
4096,
Tanh,
ReshapeLayer[{16,16,16}],
DeconvolutionLayer[32, 2, "Stride"->2],
BatchNormalizationLayer[],
Tanh,
DeconvolutionLayer[64, 2, "Stride"->2],
BatchNormalizationLayer[],
Tanh,
DeconvolutionLayer[128, 2, "Stride"->2],
BatchNormalizationLayer[],
Tanh,
DeconvolutionLayer[32, 1, "Stride"->1],
BatchNormalizationLayer[],
Tanh,
DeconvolutionLayer[3, 1, "Stride"->1],
LogisticSigmoid
}, "Input"->{nlatent}]


imageLoss = MeanSquaredLossLayer[];


latentLoss = NetGraph[
{ElementwiseLayer[-0.5*#&], TotalLayer[], ElementwiseLayer[-(#^2)&], ElementwiseLayer[-Exp[2*#]&], ElementwiseLayer[1+2*#&],SummationLayer[]},
{
NetPort["mn"]->3,
NetPort["sd"]->{4,5},
{3,4,5}->2,
2->6->1
}
];


loss = ThreadingLayer[(#+#2*3*256*256)/2&, "Output"->"Real"];


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
"dec"->NetPort["imageLoss", "Input"],
NetPort["Input"]->NetPort["imageLoss", "Target"],
(*Total loss8*)
"latentLoss"->NetPort["loss", "1"],
"imageLoss"->NetPort["loss", "2"],
"loss"->NetPort["MeanLoss"]
},
"Output"->NetDecoder[{"Image", "RGB"}],
"Input"->NetEncoder[{"Image", {width, width}, "RGB"}]
]];


imagePaths = 
Join[
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg","DataMonet"]],
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg","DataLandScape"]],
FileNames["*.jpg", "DataVanGh"],
FileNames["*.jpg", "DataCezanne"]
];
dataSets = Map[Import[#]&, imagePaths];
trainingData =<|"random"->RandomVariate[NormalDistribution[],{Length@dataSets,nlatent}],
"Input"->dataSets|>;
Echo[Length@dataSets];


dir = CreateDirectory[];
Echo[dir];


SetDirectory[NotebookDirectory[]]
trainedVae = NetTrain[vaeNet, trainingData, LossFunction->{"MeanLoss"->Scaled[1]},
MaxTrainingRounds->2000,
TrainingProgressReporting->"Print",
TargetDevice->"GPU",
Method->{"ADAM", "LearningRate"->0.0005},
TrainingProgressCheckpointing->{"Directory", dir, "Interval"->Quantity[50, "Rounds"]},
 BatchSize->32];
 Export["ultimateMonet.wlnet", trainedVae];
