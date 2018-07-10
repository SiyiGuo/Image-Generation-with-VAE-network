#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 64;
width = 256;
convChannel = 64;
kernel = 8;


encoder = NetChain[{
ReshapeLayer[{3,width,width}],
ConvolutionLayer[128, {4,4}, "Stride"->2, "PaddingSize"->1],
Tanh,
ConvolutionLayer[64, {2,2}, "Stride"->2, "PaddingSize"->1],
Tanh,
ConvolutionLayer[4, {1,1}, "Stride"->2, "PaddingSize"->1],
Tanh,
FlattenLayer[]
}];


mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];


decoder = NetChain[{
4624,
ReshapeLayer[{4,34,34}],
Tanh,
DeconvolutionLayer[64, {1,1}, "Stride"->2, "PaddingSize"->1],
Tanh,
DeconvolutionLayer[128, {4,4}, "Stride"->2, "PaddingSize"->2],
Tanh,
DeconvolutionLayer[3, {4,4}, "Stride"->2, "PaddingSize"->1],
LogisticSigmoid
}, "Input"->{nlatent}];


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


loss = ThreadingLayer[(#+#2*1*3*256*256)/2&, "Output"->"Real"];


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
Map[StringReplace[#, "\\"->"/"]&, FileNames["*.jpg","DataLandScape"]]
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
TrainingProgressCheckpointing->{"Directory", dir, "Interval"->Quantity[50, "Rounds"]},
 BatchSize->32];
 Export["finalMonet.wlnet", trainedVae];
