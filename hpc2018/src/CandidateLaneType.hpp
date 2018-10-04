//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
namespace hpc {

/// 生地置き場の種類。
enum CandidateLaneType
{
    /// 生地置き場A: 小型生地専用の生地置き場。
    CandidateLaneType_Small,
    /// 生地置き場B: 大型生地専用の生地置き場。
    CandidateLaneType_Large,

    CandidateLaneType_TERM,
};

} // namespace
// EOF
