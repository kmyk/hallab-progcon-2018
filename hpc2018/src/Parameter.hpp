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

/// ゲームのパラメータ一覧。
class Parameter
{
public:
    /// @name ステージ設定
    //@{
    /// ステージ数。
    static const int GameStageCount = 20;
    /// ステージごとのターン数。
    static const int GameTurnLimit = 1000;
    //@}

    /// @name オーブン設定
    //@{
    /// 天板の横幅。
    static const int OvenWidth = 20;
    /// 天板の縦幅。
    static const int OvenHeight = 20;
    /// 天板の面積。
    static const int OvenCellCount = OvenWidth * OvenHeight;
    //@}

    /// @name 生地設定
    //@{
    /// 生地置き場がプレイヤーに公開している生地の数。
    static const int CandidatePieceCount = 8;
    /// 生地の長辺＋短辺を折る位置の中央値の最小値。
    static const float MinPieceFoldPosRateCenter;
    /// 生地の長辺＋短辺を折る位置の中央値の最大値。
    static const float MaxPieceFoldPosRateCenter;
    /// 生地の長辺＋短辺を折る位置の幅の最小値。
    static const float MinPieceFoldPosRateRange;
    /// 生地の長辺＋短辺を折る位置の幅の最大値。
    static const float MaxPieceFoldPosRateRange;
    //@}

    /// @name 小型生地専用設定
    //@{
    /// 基準正方形の一辺の長さの最小値。
    static const int MinSmallPieceSampleEdgeLength = 2;
    /// 基準正方形の一辺の長さの最大値。
    static const int MaxSmallPieceSampleEdgeLength = 5;
    /// 原始スコアの最小値。
    static const int MinSmallPiecePrimalScore = 27;
    /// 原始スコアの最大値。
    static const int MaxSmallPiecePrimalScore = 45;
    /// スコア換算係数の中央値。
    static const float SmallPieceScoreCoeffCenter;
    /// スコア換算係数の幅。
    static const float SmallPieceScoreCoeffRange;
    //@}

    /// @name 大型生地専用設定
    //@{
    /// 基準正方形の一辺の長さの最小値。
    static const int MinLargePieceSampleEdgeLength = 7;
    /// 基準正方形の一辺の長さの最大値。
    static const int MaxLargePieceSampleEdgeLength = 10;
    /// 原始スコアの最小値。
    static const int MinLargePiecePrimalScore = 1280;
    /// 原始スコアの最大値。
    static const int MaxLargePiecePrimalScore = 1920;
    /// スコア換算係数の中央値の最小値。
    static const float MinLargePieceScoreCoeffCenter;
    /// スコア換算係数の中央値の最大値。
    static const float MaxLargePieceScoreCoeffCenter;
    /// スコア換算係数の幅。
    static const float LargePieceScoreCoeffRange;
    //@}
};

} // namespace
// EOF
