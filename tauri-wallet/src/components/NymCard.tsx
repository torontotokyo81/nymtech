import React from 'react'
import { Card, CardContent, CardHeader, useTheme } from '@material-ui/core'

export const NymCard = ({
  title,
  subheader,
  Action,
  noPadding,
  children,
}: {
  title: string
  subheader?: string
  Action?: React.ReactNode
  noPadding?: boolean
  children: React.ReactElement
}) => {
  const theme = useTheme()
  return (
    <Card variant="outlined">
      <CardHeader
        title={title}
        subheader={subheader}
        titleTypographyProps={{ variant: 'h5' }}
        subheaderTypographyProps={{ variant: 'subtitle1' }}
        action={Action}
        style={{
          padding: theme.spacing(2.5),
          borderBottom: `1px solid ${theme.palette.grey[200]}`,
        }}
      />
      <CardContent
        style={{
          background: theme.palette.grey[50],
          padding: noPadding ? 0 : theme.spacing(2, 5),
        }}
      >
        {children}
      </CardContent>
    </Card>
  )
}
