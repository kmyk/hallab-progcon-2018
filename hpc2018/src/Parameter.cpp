//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once
#include "Parameter.hpp"

//------------------------------------------------------------------------------
namespace hpc {

const float Parameter::MinPieceFoldPosRateCenter = 0.1f;
const float Parameter::MaxPieceFoldPosRateCenter = 0.9f;
const float Parameter::MinPieceFoldPosRateRange = 0.1f;
const float Parameter::MaxPieceFoldPosRateRange = 1.0f;

const float Parameter::SmallPieceScoreCoeffCenter = 0.3f;
const float Parameter::SmallPieceScoreCoeffRange = 0.1f;

const float Parameter::MinLargePieceScoreCoeffCenter = 0.3f;
const float Parameter::MaxLargePieceScoreCoeffCenter = 0.6f;
const float Parameter::LargePieceScoreCoeffRange = 0.3f;

} // namespace
// EOF
