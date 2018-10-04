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
#include "Game.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// ゲームを実行するクラス。
class Simulator
{
public:
    /// @name コンストラクタ
    //@{
    Simulator();
    //@}

    /// @name 設定
    //@{
    /// 乱数シードを変更する。
    void changeSeed(RandomSeed aSeed);
    //@}

    /// @name 実行
    //@{
    /// ゲームを実行する。
    void run();
    //@}

    /// @name 結果出力
    //@{
    /// 最終結果を表示する。
    void printResult(bool aIsSilent) const;
    /// 全ステージの進行記録を JSON で出力する。
    void printJson() const;
    //@}

    /// @name 問い合わせ
    //@{
    /// 総スコア。
    int totalScore() const;
    /// 実行にかかった時間。
    double elapsedSec() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// ゲーム本体。
    Game mGame;
    //@}
};

} // namespace
// EOF
