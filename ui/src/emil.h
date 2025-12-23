#pragma once

#include "sidebarwidget.h"
#include "uitypes.h"

class EmilSidebarWidget : public SidebarWidget {
    Q_OBJECT
    BinaryViewRef m_data;
    ViewFrame *m_currentFrame;

public:
    explicit EmilSidebarWidget(BinaryViewRef data);
    ~EmilSidebarWidget() override;
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
