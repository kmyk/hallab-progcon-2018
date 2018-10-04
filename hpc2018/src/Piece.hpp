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

/// クッキーの生地。
class Piece
{
public:
    /// @name コンストラクタ
    //@{
    Piece();
    Piece(
        const Vector2i& aPos,
        int aWidth,
        int aHeight,
        int aRequiredHeatTurnCount,
        int aScore
        );
    //@}

    /// @name 各種問い合わせ
    //@{
    /// 生地の配置位置。
    /// @detail 「生地を pos の位置に置く」とは、
    ///         まず pos の位置に生地のカドが来るように、
    ///         そしてそこから pos + Vector2i(width() - 1, width() - 1) までを
    ///         対角線とする長方形が、その生地が占有する空間となるように、
    ///         生地を配置することを意味します。
    Vector2i pos() const;
    /// 横幅。
    int width() const;
    /// 縦幅。
    int height() const;
    /// 今までに生地に与えられた加熱ターン数。
    int currentHeatTurnCount() const;
    /// 生地の完成に必要な加熱ターン数。
    int requiredHeatTurnCount() const;
    /// 生地の完成に必要な残り加熱ターン数。
    int restRequiredHeatTurnCount() const;
    /// 生地が完成したときに発生する得点。
    int score() const;
    //@}

    /// @name 内部用関数
    //@{
    /// 生地の配置位置を設定する。
    void setPos(const Vector2i& aPos);
    /// 加熱ターン数を増やす。
    void addHeatTurnCount(int aTurnCount);
    /// 完成に必要な加熱ターン数以上の加熱を受けたか？
    bool isCompleted() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// 生地の位置。
    Vector2i mPos;
    /// 横幅。
    int mWidth;
    /// 縦幅。
    int mHeight;
    /// 現在までに与えられた加熱ターン数。
    int mCurrentHeatTurnCount;
    /// 完成に必要な加熱ターン数。
    int mRequiredHeatTurnCount;
    /// 完成で得られるスコア。
    int mScore;
    //@}
};

} // namespace
// EOF
