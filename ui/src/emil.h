#pragma once

#include "sidebarwidget.h"
#include "uitypes.h"

class EmilSidebarWidget : public SidebarWidget {
    Q_OBJECT
    BinaryViewRef m_data;
    ViewFrame *m_currentFrame;
    QWidget *m_headerWidget;

public:
    explicit EmilSidebarWidget(BinaryViewRef data);
    ~EmilSidebarWidget() override;

    void notifyRefresh() override;
};

class EmilSidebarWidgetType : public SidebarWidgetType {
public:
    EmilSidebarWidgetType();

    SidebarWidgetLocation defaultLocation() const override { return SidebarWidgetLocation::LeftContent; }
    SidebarContextSensitivity contextSensitivity() const override { return PerViewTypeSidebarContext; }

    EmilSidebarWidget* createWidget(ViewFrame* viewFrame, BinaryViewRef data) override {
        return new EmilSidebarWidget(data);
    }
};
