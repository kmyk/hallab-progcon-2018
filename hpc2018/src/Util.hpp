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
#include "Vector2i.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// 便利関数群。
class Util
{
public:
    /// aLhsPos を基点とする矩形と aRhsPos を基点とする矩形が重なっているかを取得する。
    /// @detail 境界線も範囲に含みます。
    /// @return 重なっていたら true が返ります。
    /// @attention いずれかの width, height が負数の場合、正しい結果が返りません。
    ///            アサート失敗します。
    static bool IsIntersect(
        const Vector2i& aLhsPos,
        int aLhsWidth,
        int aLhsHeight,
        const Vector2i& aRhsPos,
        int aRhsWidth,
        int aRhsHeight
        );

private:
    Util();
};

} // namespace
// EOF
