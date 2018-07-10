#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 64;
width = 256;
convChannel = 64;
kernel = 8;


encoder = NetChain[{
ReshapeLayer[{3,width,width}],
ConvolutionLayer[convChannel, kernel, "Stride"->2, "PaddingSize"->2],
Tanh,
ConvolutionLayer[convChannel, kernel, "Stride"->2, "PaddingSize"->2],
Tanh,
FlattenLayer[],
576
}]


mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];


decoder = NetChain[{
576,
Tanh,
768, 
Tanh,
ReshapeLayer[{3,16,16}],
DeconvolutionLayer[64, 4, "Stride"->2,"PaddingSize"->2],
Tanh,
DropoutLayer[],
DeconvolutionLayer[convChannel, 4, "Stride"->1,"PaddingSize"->2],
Tanh,
FlattenLayer[],
3*width,
Tanh,
3*width*width,
LogisticSigmoid,
ReshapeLayer[{3,width,width}]
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


Export["denseMonet.wlnet", vaeNet]


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
 BatchSize->64];
 Export["denseMonet.wlnet", trainedVae];



